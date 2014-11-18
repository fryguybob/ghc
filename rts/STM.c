/* -----------------------------------------------------------------------------
 * (c) The GHC Team 1998-2005
 * 
 * STM implementation.
 *
 * Overview
 * --------
 *
 * See the PPoPP 2005 paper "Composable memory transactions".  In summary, 
 * each transaction has a TRec (transaction record) holding entries for each of the
 * TVars (transactional variables) that it has accessed.  Each entry records
 * (a) the TVar, (b) the expected value seen in the TVar, (c) the new value that
 * the transaction wants to write to the TVar, (d) during commit, the identity of
 * the TRec that wrote the expected value.  
 *
 * Separate TRecs are used for each level in a nest of transactions.  This allows
 * a nested transaction to be aborted without condemning its enclosing transactions.
 * This is needed in the implementation of catchRetry.  Note that the "expected value"
 * in a nested transaction's TRec is the value expected to be *held in memory* if
 * the transaction commits -- not the "new value" stored in one of the enclosing
 * transactions.  This means that validation can be done without searching through
 * a nest of TRecs.
 *
 * Concurrency control
 * -------------------
 *
 * Three different concurrency control schemes can be built according to the settings
 * in STM.h:
 * 
 * STM_UNIPROC assumes that the caller serialises invocations on the STM interface.
 * In the Haskell RTS this means it is suitable only for non-THREADED_RTS builds.
 *
 * STM_CG_LOCK uses coarse-grained locking -- a single 'stm lock' is acquired during
 * an invocation on the STM interface.  Note that this does not mean that 
 * transactions are simply serialized -- the lock is only held *within* the 
 * implementation of stmCommitTransaction, stmWait etc.
 *
 * STM_FG_LOCKS uses fine-grained locking -- locking is done on a per-TVar basis
 * and, when committing a transaction, no locks are acquired for TVars that have
 * been read but not updated.
 *
 * Concurrency control is implemented in the functions:
 *
 *    lock_stm
 *    unlock_stm
 *    lock_tvar / cond_lock_tvar
 *    unlock_tvar
 *
 * The choice between STM_UNIPROC / STM_CG_LOCK / STM_FG_LOCKS affects the 
 * implementation of these functions.  
 *
 * lock_stm & unlock_stm are straightforward : they acquire a simple spin-lock
 * using STM_CG_LOCK, and otherwise they are no-ops.
 *
 * lock_tvar / cond_lock_tvar and unlock_tvar are more complex because they 
 * have other effects (present in STM_UNIPROC and STM_CG_LOCK builds) as well
 * as the actual business of manipulating a lock (present only in STM_FG_LOCKS
 * builds).  This is because locking a TVar is implemented by writing the lock
 * holder's TRec into the TVar's current_value field:
 *
 *   lock_tvar - lock a specified TVar (STM_FG_LOCKS only), returning the value 
 *               it contained.
 *
 *   cond_lock_tvar - lock a specified TVar (STM_FG_LOCKS only) if it 
 *               contains a specified value.  Return TRUE if this succeeds,
 *               FALSE otherwise.
 *
 *   unlock_tvar - release the lock on a specified TVar (STM_FG_LOCKS only),
 *               storing a specified value in place of the lock entry.
 *
 * Using these operations, the typical pattern of a commit/validate/wait operation
 * is to (a) lock the STM, (b) lock all the TVars being updated, (c) check that 
 * the TVars that were only read from still contain their expected values, 
 * (d) release the locks on the TVars, writing updates to them in the case of a 
 * commit, (e) unlock the STM.
 *
 * ---------------------------------------------------------------------------*/

#include "PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "Schedule.h"
#include "STM.h"
#include "Trace.h"
#include "Threads.h"
#include "sm/Storage.h"

#include <stdio.h>

#include "rtm-goto.h"
#include "immintrin.h"

#define TRUE 1
#define FALSE 0

// ACQ_ASSERT is used for assertions which are only required for
// THREADED_RTS builds with fine-grained locking.

#if defined(STM_FG_LOCKS)
#define ACQ_ASSERT(_X) ASSERT(_X)
#define NACQ_ASSERT(_X) /*Nothing*/
#else
#define ACQ_ASSERT(_X) /*Nothing*/
#define NACQ_ASSERT(_X) ASSERT(_X)
#endif

/*......................................................................*/

// If SHAKE is defined then validation will sometime spuriously fail.  They helps test
// unusualy code paths if genuine contention is rare

#define TRACE(_x...) debugTrace(DEBUG_stm, "STM: " _x)

#ifdef SHAKE
static const int do_shake = TRUE;
#else
static const int do_shake = FALSE;
#endif
static int shake_ctr = 0;
static int shake_lim = 1;

static int shake(void) {
  if (do_shake) {
    if (((shake_ctr++) % shake_lim) == 0) {
      shake_ctr = 1;
      shake_lim ++;
      return TRUE;
    } 
    return FALSE;
  } else {
    return FALSE;
  }
}

/*......................................................................*/

// Helper macros for iterating over entries within a transaction
// record

#define _FOR_EACH_ENTRY(_t,_x,CODE,HEADER,CHUNK,ENTRY,END_LIST,SIZE) do {       \
  HEADER *__t = (_t);                                                           \
  CHUNK *__c = __t -> current_chunk;                                            \
  StgWord __limit = __c -> next_entry_idx;                                      \
  TRACE("%p : FOR_EACH_ENTRY, current_chunk=%p limit=%ld", __t, __c, __limit);  \
  while (__c != END_LIST) {                                                     \
    StgWord __i;                                                                \
    for (__i = 0; __i < __limit; __i ++) {                                      \
      ENTRY *_x = &(__c -> entries[__i]);                                       \
      do { CODE } while (0);                                                    \
    }                                                                           \
    __c = __c -> prev_chunk;                                                    \
    __limit = SIZE;                                                             \
  }                                                                             \
 exit_for_each:                                                                 \
  if (FALSE) goto exit_for_each;                                                \
} while (0)

#define BREAK_FOR_EACH goto exit_for_each

#define FOR_EACH_ENTRY(_t,_x,CODE)                                              \
  _FOR_EACH_ENTRY(_t,_x,CODE,StgTRecHeader,StgTRecChunk,TRecEntry               \
                 ,END_STM_CHUNK_LIST,TREC_CHUNK_NUM_ENTRIES)
/*......................................................................*/

// if REUSE_MEMORY is defined then attempt to re-use descriptors, log chunks,
// and wait queue entries without GC

#define REUSE_MEMORY

/*......................................................................*/

#define IF_STM_UNIPROC(__X)  do { } while (0)
#define IF_STM_CG_LOCK(__X)  do { } while (0)
#define IF_STM_FG_LOCKS(__X) do { } while (0)

#if defined(STM_UNIPROC)
#undef IF_STM_UNIPROC
#define IF_STM_UNIPROC(__X)  do { __X } while (0)
static const StgBool config_use_read_phase = FALSE;

static void lock_stm(StgTRecHeader *trec STG_UNUSED) {
  TRACE("%p : lock_stm()", trec);
}

static void unlock_stm(StgTRecHeader *trec STG_UNUSED) {
  TRACE("%p : unlock_stm()", trec);
}

static StgClosure *lock_tvar(StgTRecHeader *trec STG_UNUSED, 
                             StgTVar *s STG_UNUSED) {
  StgClosure *result;
  TRACE("%p : lock_tvar(%p)", trec, s);
  result = s -> current_value;
  return result;
}

static void unlock_tvar(Capability *cap,
                        StgTRecHeader *trec STG_UNUSED,
                        StgTVar *s,
                        StgClosure *c,
                        StgBool force_update) {
  TRACE("%p : unlock_tvar(%p)", trec, s);
  if (force_update) {
    s -> current_value = c;
    dirty_TVAR(cap,s);
  }
}

static StgBool cond_lock_tvar(StgTRecHeader *trec STG_UNUSED, 
                              StgTVar *s STG_UNUSED,
                              StgClosure *expected) {
  StgClosure *result;
  TRACE("%p : cond_lock_tvar(%p, %p)", trec, s, expected);
  result = s -> current_value;
  TRACE("%p : %s", trec, (result == expected) ? "success" : "failure");
  return (result == expected);
}
#endif

#if defined(STM_CG_LOCK) /*........................................*/

#undef IF_STM_CG_LOCK
#define IF_STM_CG_LOCK(__X)  do { __X } while (0)
static const StgBool config_use_read_phase = FALSE;
static volatile int smp_locked = 0;

// In the simple scheme, encountering a retry will cause a fallback to STM.
// We are not tracking the read set so we do not know what watch lists to
// go on.

// Abort reason codes:
#define ABORT_FALLBACK  1
#define ABORT_RESTART   2
#define ABORT_GC        3
#define RETRY_COUNT     5

#define HTM_LATE_LOCK_SUBSCRIPTION

static void lock_stm(StgTRecHeader *trec STG_UNUSED) {
  int i;
  for (i = 0; i < RETRY_COUNT; i++)
  {
    XBEGIN(fail);
    if (smp_locked == 0)
      return;
    XEND();
    XFAIL(fail);
  }

  while (__sync_lock_test_and_set(&smp_locked, 1))
  {
    while (smp_locked != 0)
      _mm_pause();
  }
  TRACE("%p : lock_stm()", trec);
}

static void unlock_stm(StgTRecHeader *trec STG_UNUSED) {
  TRACE("%p : unlock_stm()", trec);

  if (smp_locked == 0)
  {
    XEND();
  }
  else
  {
    __sync_lock_release(&smp_locked);
  }
}

static StgClosure *lock_tvar(StgTRecHeader *trec STG_UNUSED, 
                             StgTVar *s STG_UNUSED) {
  StgClosure *result;
  TRACE("%p : lock_tvar(%p)", trec, s);
  result = s -> current_value;
  return result;
}

static void unlock_tvar(Capability *cap,
                        StgTRecHeader *trec STG_UNUSED,
                        StgTVar *s STG_UNUSED,
                        StgClosure *c,
                        StgBool force_update) {
  TRACE("%p : unlock_tvar(%p, %p)", trec, s, c);
  if (force_update) {
    s -> current_value = c;
    dirty_TVAR(cap,s);
  }
}

static StgBool cond_lock_tvar(StgTRecHeader *trec STG_UNUSED, 
                               StgTVar *s STG_UNUSED,
                               StgClosure *expected) {
  StgClosure *result;
  TRACE("%p : cond_lock_tvar(%p, %p)", trec, s, expected);
  result = s -> current_value;
  TRACE("%p : %d", result ? "success" : "failure");
  return (result == expected);
}
#endif

#if defined(STM_FG_LOCKS) /*...................................*/

#undef IF_STM_FG_LOCKS
#define IF_STM_FG_LOCKS(__X) do { __X } while (0)
static const StgBool config_use_read_phase = TRUE;

static void lock_stm(StgTRecHeader *trec STG_UNUSED) {
  TRACE("%p : lock_stm()", trec);
}

static void unlock_stm(StgTRecHeader *trec STG_UNUSED) {
  TRACE("%p : unlock_stm()", trec);
}

static StgClosure *lock_tvar(StgTRecHeader *trec, 
                             StgTVar *s STG_UNUSED) {
  StgClosure *result;
  TRACE("%p : lock_tvar(%p)", trec, s);
  do {
    do {
      result = s -> current_value;
    } while (GET_INFO(UNTAG_CLOSURE(result)) == &stg_TREC_HEADER_info);
  } while (cas((void *)&(s -> current_value),
	       (StgWord)result, (StgWord)trec) != (StgWord)result);
  return result;
}

static void unlock_tvar(Capability *cap,
                        StgTRecHeader *trec STG_UNUSED,
                        StgTVar *s,
                        StgClosure *c,
                        StgBool force_update STG_UNUSED) {
  TRACE("%p : unlock_tvar(%p, %p)", trec, s, c);
  ASSERT(s -> current_value == (StgClosure *)trec);
  s -> current_value = c;
  dirty_TVAR(cap,s);
}

static StgBool cond_lock_tvar(StgTRecHeader *trec, 
                              StgTVar *s,
                              StgClosure *expected) {
  StgClosure *result;
  StgWord w;
  TRACE("%p : cond_lock_tvar(%p, %p)", trec, s, expected);
  w = cas((void *)&(s -> current_value), (StgWord)expected, (StgWord)trec);
  result = (StgClosure *)w;
  TRACE("%p : %s", trec, result ? "success" : "failure");
  return (result == expected);
}
#endif

/*......................................................................*/

// Helper functions for downstream allocation and initialization

static StgTRecChunk *new_stg_trec_chunk(Capability *cap) {
  StgTRecChunk *result;
  result = (StgTRecChunk *)allocate(cap, sizeofW(StgTRecChunk));
  SET_HDR (result, &stg_TREC_CHUNK_info, CCS_SYSTEM);
  result -> prev_chunk = END_STM_CHUNK_LIST;
  result -> next_entry_idx = 0;
  return result;
}

static StgTRecHeader *new_stg_trec_header(Capability *cap,
                                          StgTRecHeader *enclosing_trec) {
  StgTRecHeader *result;
  result = (StgTRecHeader *) allocate(cap, sizeofW(StgTRecHeader));
  SET_HDR (result, &stg_TREC_HEADER_info, CCS_SYSTEM);

  result -> enclosing_trec = enclosing_trec;
  result -> current_chunk = new_stg_trec_chunk(cap);

  if (enclosing_trec == NO_TREC) {
    result -> state = TREC_ACTIVE;
  } else {
    ASSERT(enclosing_trec -> state == TREC_ACTIVE ||
           enclosing_trec -> state == TREC_CONDEMNED);
    result -> state = enclosing_trec -> state;
  }

  return result;  
}

#if defined(THREADED_RTS)
static StgHTRecHeader *new_stg_htrec_header(Capability *cap) {
  StgHTRecHeader *result;
  result = (StgHTRecHeader *) allocate(cap, sizeofW(StgHTRecHeader));
  SET_HDR (result, &stg_HTREC_HEADER_info, CCS_SYSTEM);

  result -> enclosing_trec = (StgHTRecHeader*)NO_TREC;
  result -> state = TREC_ACTIVE;
  result -> write_set = 0;
  result -> read_set = 0;

  return result;
}
#endif
/*......................................................................*/

// Allocation / deallocation functions that retain per-capability lists
// of closures that can be re-used

static StgTRecChunk *alloc_stg_trec_chunk(Capability *cap) {
  StgTRecChunk *result = NULL;
  if (cap -> free_trec_chunks == END_STM_CHUNK_LIST) {
    result = new_stg_trec_chunk(cap);
  } else {
    result = cap -> free_trec_chunks;
    cap -> free_trec_chunks = result -> prev_chunk;
    result -> prev_chunk = END_STM_CHUNK_LIST;
    result -> next_entry_idx = 0;
  }
  return result;
}

static void free_stg_trec_chunk(Capability *cap, 
                                StgTRecChunk *c) {
#if defined(REUSE_MEMORY)
  c -> prev_chunk = cap -> free_trec_chunks;
  cap -> free_trec_chunks = c;
#endif
}

static StgTRecHeader *alloc_stg_trec_header(Capability *cap,
                                            StgTRecHeader *enclosing_trec) {
  StgTRecHeader *result = NULL;
  if (cap -> free_trec_headers == NO_TREC) {
    result = new_stg_trec_header(cap, enclosing_trec);
  } else {
    result = cap -> free_trec_headers;
    cap -> free_trec_headers = result -> enclosing_trec;
    result -> enclosing_trec = enclosing_trec;
    result -> current_chunk -> next_entry_idx = 0;
    if (enclosing_trec == NO_TREC) {
      result -> state = TREC_ACTIVE;
    } else {
      ASSERT(enclosing_trec -> state == TREC_ACTIVE ||
             enclosing_trec -> state == TREC_CONDEMNED);
      result -> state = enclosing_trec -> state;
    }
  }
  return result;
}

static void free_stg_trec_header(Capability *cap,
                                 StgTRecHeader *trec) {
#if defined(REUSE_MEMORY)
  StgTRecChunk *chunk = trec -> current_chunk -> prev_chunk;
  while (chunk != END_STM_CHUNK_LIST) {
    StgTRecChunk *prev_chunk = chunk -> prev_chunk;
    free_stg_trec_chunk(cap, chunk);
    chunk = prev_chunk;
  } 
  trec -> current_chunk -> prev_chunk = END_STM_CHUNK_LIST;
  trec -> enclosing_trec = cap -> free_trec_headers;
  cap -> free_trec_headers = trec;
#endif
}

#if defined(THREADED_RTS)
static StgHTRecHeader *alloc_stg_htrec_header(Capability *cap) {
  StgHTRecHeader *result = NULL;
  result = new_stg_htrec_header(cap);
  return result;
}

static void free_stg_htrec_header(Capability *cap STG_UNUSED,
                                 StgHTRecHeader *trec STG_UNUSED) {
}
#endif
/*......................................................................*/

static TRecEntry *get_new_entry(Capability *cap,
                                StgTRecHeader *t) {
  TRecEntry *result;
  StgTRecChunk *c;
  int i;

  c = t -> current_chunk;
  i = c -> next_entry_idx;
  ASSERT(c != END_STM_CHUNK_LIST);

  if (i < TREC_CHUNK_NUM_ENTRIES) {
    // Continue to use current chunk
    result = &(c -> entries[i]);
    c -> next_entry_idx ++;
  } else {
    // Current chunk is full: allocate a fresh one
    StgTRecChunk *nc;
    nc = alloc_stg_trec_chunk(cap);
    nc -> prev_chunk = c;
    nc -> next_entry_idx = 1;
    t -> current_chunk = nc;
    result = &(nc -> entries[0]);
  }

  return result;
}

/*......................................................................*/
#if defined(THREADED_RTS)
// TODO: Lots of work needed here.  How to hash and which hash functions
// should depend on the size of the filter etc.  Right now this is just
// something to get stuff working.

#define HTM_RETRY_COMMIT_WITH_LOCK

static volatile int smp_locked_bloom = 0;

static void lock_bloom(void) {
  while (__sync_lock_test_and_set(&smp_locked_bloom, 1))
  {
    while (smp_locked_bloom != 0)
      _mm_pause();
  }
}

#ifdef HTM_RETRY_COMMIT_WITH_LOCK
static void lock_bloom_in_htm(void) {
  if (smp_locked_bloom != 0)
  {
    XABORT(ABORT_RESTART);
  }
  smp_locked_bloom = 1;
}
#endif

static void lock_bloom_hle(void) {
  int i;
  for (i = 0; i < RETRY_COUNT; i++)
  {
    XBEGIN(fail);
    if (smp_locked_bloom == 0)
      return;
    XEND();
    XFAIL(fail);
  }

  lock_bloom();
}

static void unlock_bloom(void) {
  __sync_lock_release(&smp_locked_bloom);
}

static void unlock_bloom_hle(void) {
  if (smp_locked_bloom == 0)
  {
    XEND();
  }
  else
  {
    unlock_bloom();
  }
}
#else // !THREADED_RTS

static void lock_bloom(void) {
}

static void unlock_bloom(void) {
}

#endif // !THREADED_RTS

#define BLOOM_BIT_COUNT     64 // TODO: Bold assumption.

static StgWord hash1(StgWord w) { return 1 << ((w & 0x00003f0) >>  4); }
static StgWord hash2(StgWord w) { return 1 << ((w & 0x003f000) >> 12); }
static StgWord hash3(StgWord w) { return 1 << ((w & 0x3f00000) >> 20); }

// Bloom filters for wakeups
static StgBloom bloom_add(StgBloom filter, StgTVar *tvar)
{
    StgWord w = tvar->hash_id;
    return filter | hash1(w) | hash2(w) | hash3(w);
}

// TODO: this structure will be used to insert new
// filters for blocked transactions when they commit in HTM on
// `retry`.  When a transaction commits with writes, we will
// wake up threads with transactions who's write-set matches
// any filter.  We can't miss any wakeups!  So we have to be
// on this structure when a transaction commits on `retry`.
// But we don't want this structure to cause any unnecessary
// conflicts that kill off a transaction.  Extra wakeups are
// not a problem, but missing a wakeup is a problem.
//
// Another important question that must be answered is when
// a filter can be removed from the queue.  Since we have lost
// the actual read-set and we don't have a trec like in the case
// of STM we can remove it as soon as any transaction could wake
// it up.  It will run at some point in the future and if it fails
// to get passed the `retry` will insert itself back on the queue
// at the end.
StgBloomWakeupChunk *smp_bloomWakeupList = END_BLOOM_WAKEUP_CHUNK_LIST;

static StgBloomWakeupChunk *new_stg_bloom_wakeup_chunk(Capability *cap) {
  StgBloomWakeupChunk *result;
  result = (StgBloomWakeupChunk *)allocate(cap, sizeofW(StgBloomWakeupChunk));
  SET_HDR (result, &stg_BLOOM_WAKEUP_CHUNK_info, CCS_SYSTEM);
  result -> prev_chunk = END_BLOOM_WAKEUP_CHUNK_LIST;
  result -> next_entry_idx = 0;
  return result;
}

void markWakeupSTM (evac_fn evac, void *user)
{
    evac(user, (StgClosure **)&smp_bloomWakeupList);
}

// We have a few schemes for getting read sets into the global
// list of blocked threads. 
//
// 1) The first has the read-only transaction which blocks on a `retry` take
//    the bloom lock before XEND.  We then have a committed transaction *and*
//    hold the bloom lock.  We can then insert our filter and release the lock.
//
//    The risk is contention on the bloom lock might cause the `retry`
//    transaction to fail to commit.  The portion of execution where we are
//    waking up 
//
//    The benefit, we can offload the risk by having the bloom lock elided with
//    a transaction for wakeups.  We won't actually take a lock for wakeup
//    until we have several failures.  This means we avoid impeding the
//    *user's* transactions by making the wakeup speculative while still
//    closing the window for a write to commit before a `retry` transaction has
//    had a chance to put itself on the watch queue.
//
// 2) The second option does the work of inserting inside the transaction.  The
//    risk is we may kill the `retry` transaction with a conflict in the bloom data
//    structure.
//
// 3) Ala RingSTM.  We can leave a gap where we are not on the global list of
//    read-sets as long as we know what happens between when we commit and when
//    we do get on the list.  Writers could then write their write-sets to a
//    buffer with a marker indicating the current location of the last write.
//    Inside the read-only transaction we read the marker and commit.  Then
//    after adding the read-set, we look to see if the marker has moved.  If it
//    has, we know exactly which write-sets to compare with.
//
//    It isn't clear how much this solves the contention problem as we still
//    have to read this marker and do more work then if we just have the lock
//    and add ourselves as in scheme (1).
//
static void bloom_insert(Capability *cap, StgBloom filter, StgTSO* tso)
{
    StgBloomWakeupChunk *q = smp_bloomWakeupList;
    StgWord i;
    if (q != END_BLOOM_WAKEUP_CHUNK_LIST)
    {
        i = q -> next_entry_idx;
    }
    else
    {
        i = BLOOM_WAKEUP_CHUNK_NUM_ENTRIES;
    }

    if (i >= BLOOM_WAKEUP_CHUNK_NUM_ENTRIES)
    {
        i = 0;
        TRACE("Adding new bloom wakeup chunk.");
        q = new_stg_bloom_wakeup_chunk(cap);
        q -> prev_chunk = smp_bloomWakeupList;
        smp_bloomWakeupList = q;
    }

    TRACE("Inserting readset %p with TSO %p at index %d.", filter, tso, i);
    q -> filters[i].filter = filter;
    q -> filters[i].tso = tso;
    q -> next_entry_idx++;
}

static StgBool bloom_match(StgBloom a, StgBloom b)
{
    return (a & b) != 0;
}


static void unpark_tso(Capability *cap, StgTSO *tso);

// Wake up and remove any blocked transactions who's read sets
// overlap with write sets.
static void bloom_wakeup(Capability *cap, StgBloom filter)
{
    if (filter == 0)
        return;

#ifdef THREADED_RTS
    lock_bloom_hle();
#endif

    StgWord i;
    StgBloomWakeupChunk *q, *prev;
    q = smp_bloomWakeupList;
    prev = NULL;


    for (; q != END_BLOOM_WAKEUP_CHUNK_LIST; prev = q, q = q -> prev_chunk)
    {
        StgBool dead = TRUE;

        for (i = 0; i < q -> next_entry_idx; i++)
        {
            if (q -> filters[i].filter != 0)
            {
                // TODO: Here we are checking if the intersection of
                // these two filters (read set and write set) is empty.
                // This is an approximate check, but if it says "yes"
                // it is empty, it is accurate.  If it says "no" it may
                // still be empty.  This is ok for wakeup, but we could
                // be more accurate if we had a filter for each write
                // but this is exactly the whole write set.  We want to
                // use constant space though.  Perhaps there is something
                // better...
                if (bloom_match(filter, q -> filters[i].filter))
                {
                    // wakeup.
                    // TODO: HLE the TSO lock?  Make some simpler
                    // way of doing the wakeup?  have a local queue for
                    // waking up?
                    unpark_tso(cap, q -> filters[i].tso);

                    // mark for removal.
                    q -> filters[i].filter = 0;
                    q -> filters[i].tso = NULL;
                }
                else
                {
                    // the valid filter in the other branch of this
                    // if was removed, so we do not want to count that
                    // filter as keeping this chunk alive.
                    dead = FALSE;
                }
            }
        }

        if (dead)
        {
            // The chunk we just finished processing has no valid
            // entries in it.  We can unlink it.
            if (prev == NULL)
            {
                smp_bloomWakeupList = q -> prev_chunk;
            }
            else
            {
                prev -> prev_chunk = q -> prev_chunk;
            }
        }
    }

#ifdef THREADED_RTS
    unlock_bloom_hle();
#endif
}

static StgBloom bloom_readset(StgTRecHeader* trec)
{
    StgBloom filter = 0;

    FOR_EACH_ENTRY(trec, e, {
        filter = bloom_add(filter, e -> tvar);
    });

    return filter;
}

/*......................................................................*/
 
// Helper functions for thread blocking and unblocking

static void park_tso(StgTSO *tso) {
  ASSERT(tso -> why_blocked == NotBlocked);
  tso -> why_blocked = BlockedOnSTM;
  tso -> block_info.closure = (StgClosure *) END_TSO_QUEUE;
  TRACE("park_tso on tso=%p", tso);
}

static void unpark_tso(Capability *cap, StgTSO *tso) {
    // We will continue unparking threads while they remain on one of the wait
    // queues: it's up to the thread itself to remove it from the wait queues
    // if it decides to do so when it is scheduled.

    // Unblocking a TSO from BlockedOnSTM is done under the TSO lock,
    // to avoid multiple CPUs unblocking the same TSO, and also to
    // synchronise with throwTo(). The first time the TSO is unblocked
    // we mark this fact by setting block_info.closure == STM_AWOKEN.
    // This way we can avoid sending further wakeup messages in the
    // future.
    lockTSO(tso); // TODO: HLE!
    if (tso->why_blocked == BlockedOnSTM &&
        tso->block_info.closure == &stg_STM_AWOKEN_closure) {
      TRACE("unpark_tso already woken up tso=%p", tso);
    } else if (tso -> why_blocked == BlockedOnSTM) {
      TRACE("unpark_tso on tso=%p", tso);
      tso->block_info.closure = &stg_STM_AWOKEN_closure;
      tryWakeupThread(cap,tso);
    } else {
      TRACE("spurious unpark_tso on tso=%p", tso);
    }
    unlockTSO(tso);
}

static void unpark_waiters_on(Capability *cap, StgTVar *s) {
    // We have a write, wake up any filters that include
    // the TVar being written.
    // TODO: Locking?
    bloom_wakeup(cap, bloom_add(0, s));
}


/*......................................................................*/

static void merge_update_into(Capability *cap,
                              StgTRecHeader *t,
                              StgTVar *tvar,
                              StgClosure *expected_value,
                              StgClosure *new_value) {
  int found;
  
  // Look for an entry in this trec
  found = FALSE;
  FOR_EACH_ENTRY(t, e, {
    StgTVar *s;
    s = e -> tvar;
    if (s == tvar) {
      found = TRUE;
      if (e -> expected_value != expected_value) {
        // Must abort if the two entries start from different values
        TRACE("%p : update entries inconsistent at %p (%p vs %p)", 
              t, tvar, e -> expected_value, expected_value);
        t -> state = TREC_CONDEMNED;
      } 
      e -> new_value = new_value;
      BREAK_FOR_EACH;
    }
  });

  if (!found) {
    // No entry so far in this trec
    TRecEntry *ne;
    ne = get_new_entry(cap, t);
    ne -> tvar = tvar;
    ne -> expected_value = expected_value;
    ne -> new_value = new_value;
  }
}

/*......................................................................*/

static void merge_read_into(Capability *cap,
                            StgTRecHeader *trec,
			    StgTVar *tvar,
                            StgClosure *expected_value)
{
  int found;
  StgTRecHeader *t;

  found = FALSE;

  //
  // See #7493
  //
  // We need to look for an existing entry *anywhere* in the stack of
  // nested transactions.  Otherwise, in stmCommitNestedTransaction()
  // we can't tell the difference between
  //
  //   (1) a read-only entry
  //   (2) an entry that writes back the original value
  //
  // Since in both cases e->new_value == e->expected_value. But in (1)
  // we want to do nothing, and in (2) we want to update e->new_value
  // in the outer transaction.
  //
  // Here we deal with the first possibility: we never create a
  // read-only entry in an inner transaction if there is an existing
  // outer entry; so we never have an inner read and an outer update.
  // So then in stmCommitNestedTransaction() we know we can always
  // write e->new_value over the outer entry, because the inner entry
  // is the most up to date.
  //
  for (t = trec; !found && t != NO_TREC; t = t -> enclosing_trec)
  {
    FOR_EACH_ENTRY(t, e, {
      if (e -> tvar == tvar) {
        found = TRUE;
        if (e -> expected_value != expected_value) {
            // Must abort if the two entries start from different values
            TRACE("%p : read entries inconsistent at %p (%p vs %p)",
                  t, tvar, e -> expected_value, expected_value);
            t -> state = TREC_CONDEMNED;
        }
        BREAK_FOR_EACH;
      }
    });
  }

  if (!found) {
    // No entry found
    TRecEntry *ne;
    ne = get_new_entry(cap, trec);
    ne -> tvar = tvar;
    ne -> expected_value = expected_value;
    ne -> new_value = expected_value;
  }
}

/*......................................................................*/

static StgBool entry_is_update(TRecEntry *e) {
  StgBool result;
  result = (e -> expected_value != e -> new_value);
  return result;
} 

#if defined(STM_FG_LOCKS)
static StgBool entry_is_read_only(TRecEntry *e) {
  StgBool result;
  result = (e -> expected_value == e -> new_value);
  return result;
} 

static StgBool tvar_is_locked(StgTVar *s, StgTRecHeader *h) {
  StgClosure *c;
  StgBool result;
  c = s -> current_value;
  result = (c == (StgClosure *) h);
  return result;  
}
#endif

// revert_ownership : release a lock on a TVar, storing back
// the value that it held when the lock was acquired.  "revert_all"
// is set in stmWait and stmReWait when we acquired locks on all of 
// the TVars involved.  "revert_all" is not set in commit operations
// where we don't lock TVars that have been read from but not updated.

static void revert_ownership(Capability *cap STG_UNUSED,
                             StgTRecHeader *trec STG_UNUSED,
                             StgBool revert_all STG_UNUSED) {
#if defined(STM_FG_LOCKS) 
  FOR_EACH_ENTRY(trec, e, {
    if (revert_all || entry_is_update(e)) {
      StgTVar *s;
      s = e -> tvar;
      if (tvar_is_locked(s, trec)) {
          unlock_tvar(cap, trec, s, e -> expected_value, TRUE);
      }
    }
  });
#endif
}

/*......................................................................*/

// validate_and_acquire_ownership : this performs the twin functions
// of checking that the TVars referred to by entries in trec hold the
// expected values and:
// 
//   - locking the TVar (on updated TVars during commit, or all TVars
//     during wait)
//
//   - recording the identity of the TRec who wrote the value seen in the
//     TVar (on non-updated TVars during commit).  These values are 
//     stashed in the TRec entries and are then checked in check_read_only
//     to ensure that an atomic snapshot of all of these locations has been
//     seen.

static StgBool validate_and_acquire_ownership (Capability *cap,
                                               StgTRecHeader *trec,
                                               int acquire_all,
                                               int retain_ownership) {
  StgBool result;

  if (shake()) {
    TRACE("%p : shake, pretending trec is invalid when it may not be", trec);
    return FALSE;
  }

  ASSERT ((trec -> state == TREC_ACTIVE) || 
	  (trec -> state == TREC_WAITING) ||
	  (trec -> state == TREC_CONDEMNED));
  result = !((trec -> state) == TREC_CONDEMNED);
  if (result) {
    FOR_EACH_ENTRY(trec, e, {
      StgTVar *s;
      s = e -> tvar;
      if (acquire_all || entry_is_update(e)) {
        TRACE("%p : trying to acquire %p", trec, s);
        if (!cond_lock_tvar(trec, s, e -> expected_value)) {
          TRACE("%p : failed to acquire %p", trec, s);
          result = FALSE;
          BREAK_FOR_EACH;
        }
      } else {
        ASSERT(config_use_read_phase);
        IF_STM_FG_LOCKS({
          TRACE("%p : will need to check %p", trec, s);
          if (s -> current_value != e -> expected_value) {
            TRACE("%p : doesn't match", trec);
            result = FALSE;
            BREAK_FOR_EACH;
          }
        });
      }
    });
  }

  if ((!result) || (!retain_ownership)) {
      revert_ownership(cap, trec, acquire_all);
  }
  
  return result;
}

// check_read_only : check that we've seen an atomic snapshot of the
// non-updated TVars accessed by a trec.  This checks that the last TRec to
// commit an update to the TVar is unchanged since the value was stashed in
// validate_and_acquire_ownership.  If no update is seen to any TVar than
// all of them contained their expected values at the start of the call to
// check_read_only.
//
// The paper "Concurrent programming without locks" (under submission), or
// Keir Fraser's PhD dissertation "Practical lock-free programming" discuss
// this kind of algorithm.

static StgBool check_read_only(StgTRecHeader *trec STG_UNUSED) {
  StgBool result = TRUE;

  ASSERT (config_use_read_phase);
  IF_STM_FG_LOCKS({
    FOR_EACH_ENTRY(trec, e, {
      StgTVar *s;
      s = e -> tvar;
      if (entry_is_read_only(e)) {
        TRACE("%p : check_read_only for TVar %p", trec, s);
        
        // Note we need both checks and in this order as the TVar could be
        // locked by another transaction that is committing but has not yet
        // incremented `num_updates` (See #7815).  This means `num_updates`
        // does not achieve the desired optimization, so we have removed it.
        if (s -> current_value != e -> expected_value) {
          TRACE("%p : mismatch", trec);
          result = FALSE;
          BREAK_FOR_EACH;
        }
      }
    });
  });

  return result;
}


/************************************************************************/

void stmPreGCHook (Capability *cap) {
  lock_stm(NO_TREC);
  TRACE("stmPreGCHook");
  cap->free_trec_chunks = END_STM_CHUNK_LIST;
  cap->free_trec_headers = NO_TREC;
  unlock_stm(NO_TREC);
}

/************************************************************************/

// check_read_only relies on version numbers held in TVars' "num_updates" 
// fields not wrapping around while a transaction is committed.  The version
// number is incremented each time an update is committed to the TVar
// This is unlikely to wrap around when 32-bit integers are used for the counts, 
// but to ensure correctness we maintain a shared count on the maximum
// number of commit operations that may occur and check that this has 
// not increased by more than 2^32 during a commit.

#define TOKEN_BATCH_SIZE 1024

static volatile StgInt64 max_commits = 0;

#if defined(THREADED_RTS)
static volatile StgWord token_locked = FALSE;

static void getTokenBatch(Capability *cap) {
  while (cas((void *)&token_locked, FALSE, TRUE) == TRUE) { /* nothing */ }
  max_commits += TOKEN_BATCH_SIZE;
  TRACE("%p : cap got token batch, max_commits=%" FMT_Int64, cap, max_commits);
  cap -> transaction_tokens = TOKEN_BATCH_SIZE;
  token_locked = FALSE;
}

static void getToken(Capability *cap) {
  if (cap -> transaction_tokens == 0) {
    getTokenBatch(cap);
  }
  cap -> transaction_tokens --;
}
#else
static void getToken(Capability *cap STG_UNUSED) {
  // Nothing
}
#endif

/*......................................................................*/

StgTRecHeader *stmStartTransaction(Capability *cap,
                                   StgTRecHeader *outer) {

  // We will leave this function in two possible states:
  //
  // 1) Execution is in a hardware transaction and the return value is an
  //    StgHTRecHeader*
  //
  // 2) Execution is in a software transaction and the return value is an
  //    StgTRecHeader*
  //
#if defined(THREADED_RTS)
  if (XTEST()) {
    // TODO: Nest HTM

    // For the simple version abort when nesting.  More
    // complicated versions can use STM inside a hardware
    // transaction.
    XABORT(ABORT_FALLBACK);
  }
  else if (outer == NO_TREC)
  {
    // We check for an outer transaction to avoid starting an HTM transaction
    // nested in an STM transaction.
    int i, s;
    StgHTRecHeader *th;
    th = alloc_stg_htrec_header(cap);
    TRACE("%p : stmStartTransaction()=%p XBEGIN", outer, th);
    for (i = 0; i < RETRY_COUNT; i++) {
      XBEGIN(fail); // Aborted transaction will go to the XFAIL_STATUS line below.
#ifndef HTM_LATE_LOCK_SUBSCRIPTION
      if (smp_locked != 0) {
          // Early Lock subscription.
          // Make sure that no STM transaction is committing while we run.
          XABORT(ABORT_RESTART);
      }
#endif // !HTM_LATE_LOCK_SUBSCRIPTION
      return (StgTRecHeader*)th;
     
      int status;
      XFAIL_STATUS(fail, status);
      s = status & 0xffffff;
      TRACE("%p : XFAIL %x %x %d", outer, status, s, XABORT_CODE(status));
      if ((s == XABORT_EXPLICIT && XABORT_CODE(status) == ABORT_FALLBACK) 
        || s != XABORT_RETRY) {
          break;
      }
      else
      {
          // Perhaps our failure was due to observing the lock from a committing
          // STM transaction.  Wait until we observe the lock free.  If we do not
          // do this we risk all transactions falling back.
          while (smp_locked != 0)
              _mm_pause(); // We should have some backoff here.
      }
    }
    free_stg_htrec_header(cap, th);
  }
#endif

  TRACE("%p : stmStartTransaction with %d tokens", 
        outer, 
        cap -> transaction_tokens);

  getToken(cap);

  StgTRecHeader* t;
  t = alloc_stg_trec_header(cap, outer);
  TRACE("%p : stmStartTransaction()=%p", outer, t);
  return t;
}

/*......................................................................*/

void stmAbortTransaction(Capability *cap,
                         StgTRecHeader *trec) {
  StgTRecHeader *et;

#if defined(THREADED_RTS)
  if (XTEST()) {
    XABORT(ABORT_FALLBACK);
  }
#endif

  TRACE("%p : stmAbortTransaction", trec);
  ASSERT (trec != NO_TREC);
  ASSERT ((trec -> state == TREC_ACTIVE) || 
          (trec -> state == TREC_WAITING) ||
          (trec -> state == TREC_CONDEMNED));

  lock_stm(trec);

  et = trec -> enclosing_trec;
  if (et == NO_TREC) {
    // We're a top-level transaction: remove any watch queue entries that
    // we may have.
    TRACE("%p : aborting top-level transaction", trec);

    if (trec -> state == TREC_WAITING) {
      ASSERT (trec -> enclosing_trec == NO_TREC);
      TRACE("%p : stmAbortTransaction aborting waiting transaction", trec);
      // TODO: remove read_set from filters?  We used to remove entries
      // in watch queues here.
    } 

  } else {
    // We're a nested transaction: merge our read set into our parent's
    TRACE("%p : retaining read-set into parent %p", trec, et);

    FOR_EACH_ENTRY(trec, e, {
      StgTVar *s = e -> tvar;
      merge_read_into(cap, et, s, e -> expected_value);
    });
  } 

  trec -> state = TREC_ABORTED;
  unlock_stm(trec);

  TRACE("%p : stmAbortTransaction done", trec);
}

/*......................................................................*/

void stmFreeAbortedTRec(Capability *cap,
			StgTRecHeader *trec) {

  // trec could be a trec header or an htrec header.
  if (GET_INFO(UNTAG_CLOSURE((StgClosure*)trec)) != &stg_TREC_HEADER_info)
    return;

  TRACE("%p : stmFreeAbortedTRec", trec);
  ASSERT (trec != NO_TREC);
  ASSERT ((trec -> state == TREC_CONDEMNED) ||
	  (trec -> state == TREC_ABORTED));

  free_stg_trec_header(cap, trec);

  TRACE("%p : stmFreeAbortedTRec done", trec);
}

/*......................................................................*/

void stmCondemnTransaction(Capability *cap STG_UNUSED,
                           StgTRecHeader *trec) {
#if defined(THREADED_RTS)
  if (XTEST()) {
    XABORT(ABORT_FALLBACK);
  }
#endif

  TRACE("%p : stmCondemnTransaction", trec);
  ASSERT (trec != NO_TREC);
  ASSERT ((trec -> state == TREC_ACTIVE) || 
          (trec -> state == TREC_WAITING) ||
          (trec -> state == TREC_CONDEMNED));

  lock_stm(trec);
  if (trec -> state == TREC_WAITING) {
    ASSERT (trec -> enclosing_trec == NO_TREC);
    TRACE("%p : stmCondemnTransaction condemning waiting transaction", trec);
    // TODO: Remove read_set from filters?  We used to remove watch queue entries
    // here.
  } 
  trec -> state = TREC_CONDEMNED;
  unlock_stm(trec);

  TRACE("%p : stmCondemnTransaction done", trec);
}

/*......................................................................*/

StgBool stmValidateNestOfTransactions(Capability *cap, StgTRecHeader *trec) {
  StgTRecHeader *t;
  StgBool result;

#if defined(THREADED_RTS)
  if (XTEST()) {
    // This is called from either an exception or a long running transaction.
    // TODO: The long running transaction might be ok, but is likely to abort
    // before rescheduled. 
    XABORT(ABORT_FALLBACK);
  }
  else
  {
    ASSERT (GET_INFO(UNTAG_CLOSURE((StgClosure*)trec)) == &stg_TREC_HEADER_info);
  }
#endif

  TRACE("%p : stmValidateNestOfTransactions", trec);
  ASSERT(trec != NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) || 
         (trec -> state == TREC_WAITING) ||
         (trec -> state == TREC_CONDEMNED));

  lock_stm(trec);

  t = trec;
  result = TRUE;
  while (t != NO_TREC) {
    result &= validate_and_acquire_ownership(cap, t, TRUE, FALSE);
    t = t -> enclosing_trec;
  }

  if (!result && trec -> state != TREC_WAITING) {
    trec -> state = TREC_CONDEMNED; 
  }

  unlock_stm(trec);

  TRACE("%p : stmValidateNestOfTransactions()=%d", trec, result);
  return result;
}

/*......................................................................*/

static TRecEntry *get_entry_for(StgTRecHeader *trec, StgTVar *tvar, StgTRecHeader **in) {
  TRecEntry *result = NULL;

  TRACE("%p : get_entry_for TVar %p", trec, tvar);
  ASSERT(trec != NO_TREC);

  do {
    FOR_EACH_ENTRY(trec, e, {
      if (e -> tvar == tvar) {
        result = e;
        if (in != NULL) {
          *in = trec;
        }
        BREAK_FOR_EACH;
      }
    });
    trec = trec -> enclosing_trec;
  } while (result == NULL && trec != NO_TREC);

  return result;    
}

/*......................................................................*/

#if defined(THREADED_RTS)
static StgBool htmCommitTransaction(Capability *cap, StgTRecHeader *trec) {

#ifdef HTM_LATE_LOCK_SUBSCRIPTION
  // At some point we need to make sure that the fallback lock is in our
  // transaction's read set.  By reading it as late as possible we narrow
  // the window of conflict and can allow a fully-software transaction to 
  // commit while a hardware transaction runs up to this point.  The danger
  // is that the hardware transaction may be exposed to inconsistent view
  // of data.
  //
  // TODO: Prove that an inconsistent view of data in a hardware transaction
  // cannot lead to execution of an XEND instruction.  This proof would also
  // need to exclude the possiblity of execution of uninitalized data or jumping
  // to arbitrary code.  I think we should be happy by only concerning ourselves
  // with "safe" transactions.
  if (smp_locked != 0)
  {
    // A software transaction is committing or a hardware transaction is
    // waking up waiters or performing the GC write barrier on the fully-
    // software code path.
    XABORT(XABORT_RETRY);
  }
#endif // HTM_LATE_LOCK_SUBSCRIPTION

  // Commit the transaction.
  XEND();

  ASSERT(GET_INFO(UNTAG_CLOSURE((StgClosure*)trec)) == &stg_HTREC_HEADER_info);

  StgHTRecHeader *htrec = (StgHTRecHeader*)trec;

  if (htrec -> write_set != 0)
  { // Hardware transaction did some writes, we need to check for wake ups.
    bloom_wakeup(cap, htrec -> write_set);
    // TODO: GC write barrier (dirty_TVAR)!  Without it a long lived TVar can
    // be promoted to a late generation and if it becomes the only reference to
    // a value in a younger generation, that value could be collected out from
    // under it.
    //
    // The problem is we want to avoid the memory overhead of recording the
    // location of every write (we might just give up and do that though).  And
    // we can't just do the GC barrier inside the transaction as it simply
    // records the TVar, but on a list that could become a source of
    // contention if it needs to allocate more room on the Capability.  We can
    // gain some benefit if we do bother to record the write set by waking up
    // per-write and having less falls positives in our bloom filter.
    //
    // Another tact we can take is to check writes to TVars and only record
    // them if the value's generation differs.  I doubt the risk of further
    // contention from the reads to figure this out would be worth it.
    //
    // This at least serves as a point of comparison for the best case if we
    // did have some other method of handling the GC issue.
    //
    //
  }

  free_stg_htrec_header(cap, htrec);

  return TRUE;
}
#endif

/*......................................................................*/

StgBool stmCommitTransaction(Capability *cap, StgTRecHeader *trec) {
  int result;

#if defined(THREADED_RTS)
  if (XTEST()) {
    return htmCommitTransaction(cap, trec);
  }
#endif

  StgInt64 max_commits_at_start = max_commits;

  TRACE("%p : stmCommitTransaction()", trec);
  ASSERT (trec != NO_TREC);

  lock_stm(trec);

  ASSERT (trec -> enclosing_trec == NO_TREC);
  ASSERT ((trec -> state == TREC_ACTIVE) || 
          (trec -> state == TREC_CONDEMNED));

  // Use a read-phase (i.e. don't lock TVars we've read but not updated) if
  // the configueration lets us use a read phase.

  result = validate_and_acquire_ownership(cap, trec, (!config_use_read_phase), TRUE);
  if (result) {
    // We now know that all the updated locations hold their expected values.
    ASSERT (trec -> state == TREC_ACTIVE);

    if (config_use_read_phase) {
      StgInt64 max_commits_at_end;
      StgInt64 max_concurrent_commits;
      TRACE("%p : doing read check", trec);
      result = check_read_only(trec);
      TRACE("%p : read-check %s", trec, result ? "succeeded" : "failed");

      max_commits_at_end = max_commits;
      max_concurrent_commits = ((max_commits_at_end - max_commits_at_start) +
                                (n_capabilities * TOKEN_BATCH_SIZE));
      if (((max_concurrent_commits >> 32) > 0) || shake()) {
        result = FALSE;
      }
    }
    
    if (result) {
      // We now know that all of the read-only locations held their exepcted values
      // at the end of the call to validate_and_acquire_ownership.  This forms the
      // linearization point of the commit.

      // Make the updates required by the transaction
      FOR_EACH_ENTRY(trec, e, {
        StgTVar *s;
        s = e -> tvar;
        if ((!config_use_read_phase) || (e -> new_value != e -> expected_value)) {
          // Either the entry is an update or we're not using a read phase:
	  // write the value back to the TVar, unlocking it if necessary.

          ACQ_ASSERT(tvar_is_locked(s, trec));
          TRACE("%p : writing %p to %p, waking waiters", trec, e -> new_value, s);
          unpark_waiters_on(cap,s);
          unlock_tvar(cap, trec, s, e -> new_value, TRUE);
        } 
        ACQ_ASSERT(!tvar_is_locked(s, trec));
      });
    } else {
        revert_ownership(cap, trec, FALSE);
    }
  } 

  unlock_stm(trec);

  free_stg_trec_header(cap, trec);

  TRACE("%p : stmCommitTransaction()=%d", trec, result);

  return result;
}

/*......................................................................*/

StgBool stmCommitNestedTransaction(Capability *cap, StgTRecHeader *trec) {
  StgTRecHeader *et;
  int result;

#if defined(THREADED_RTS)
  if (XTEST()) {
    return TRUE;
  }
#endif

  ASSERT (trec != NO_TREC && trec -> enclosing_trec != NO_TREC);
  TRACE("%p : stmCommitNestedTransaction() into %p", trec, trec -> enclosing_trec);
  ASSERT ((trec -> state == TREC_ACTIVE) || (trec -> state == TREC_CONDEMNED));

  lock_stm(trec);

  et = trec -> enclosing_trec;
  result = validate_and_acquire_ownership(cap, trec, (!config_use_read_phase), TRUE);
  if (result) {
    // We now know that all the updated locations hold their expected values.

    if (config_use_read_phase) {
      TRACE("%p : doing read check", trec);
      result = check_read_only(trec);
    }
    if (result) {
      // We now know that all of the read-only locations held their exepcted values
      // at the end of the call to validate_and_acquire_ownership.  This forms the
      // linearization point of the commit.

      TRACE("%p : read-check succeeded", trec);
      FOR_EACH_ENTRY(trec, e, {
	// Merge each entry into the enclosing transaction record, release all
	// locks.
	
	StgTVar *s;
	s = e -> tvar;
	if (entry_is_update(e)) {
            unlock_tvar(cap, trec, s, e -> expected_value, FALSE);
	}
	merge_update_into(cap, et, s, e -> expected_value, e -> new_value);
	ACQ_ASSERT(s -> current_value != (StgClosure *)trec);
      });
    } else {
        revert_ownership(cap, trec, FALSE);
    }
  } 

  unlock_stm(trec);

  free_stg_trec_header(cap, trec);

  TRACE("%p : stmCommitNestedTransaction()=%d", trec, result);

  return result;
}

/*......................................................................*/
#if defined(THREADED_RTS)
void htmWait(Capability *cap, StgTSO *tso, StgHTRecHeader *htrec) {

  lock_bloom_in_htm(); // Take the bloom filter lock

#ifdef HTM_LATE_LOCK_SUBSCRIPTION
  if (smp_locked != 0)
  {
    XABORT(XABORT_RETRY);
  }
#endif // HTM_LATE_LOCK_SUBSCRIPTION
  // Commit the read-only transaction.
  XEND();

  // TODO: We need to avoid this.  It is in place to prevent a wakeup of a TSO before
  // it is actually sleeping properly.  Perhaps we could use a lock per entry to mark
  // the TSO as ready to wake and any waker will spin on that before waking.
  lock_stm((StgTRecHeader*)htrec);
  // We are now executing non-transactionally and have the bloom filter
  // lock.
  bloom_insert(cap, htrec -> read_set, tso);
  park_tso(tso);
  htrec -> state = TREC_WAITING;
  
  unlock_bloom();
}
#endif // THREADED_RTS

StgBool stmWait(Capability *cap, StgTSO *tso, StgTRecHeader *trec) {
  int result;

#if defined(THREADED_RTS)
  if (XTEST()) {
    XABORT(ABORT_FALLBACK);
  }
#endif

  TRACE("%p : stmWait(%p)", trec, tso);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> enclosing_trec == NO_TREC);
  ASSERT ((trec -> state == TREC_ACTIVE) || 
          (trec -> state == TREC_CONDEMNED));

  lock_stm(trec);
  result = validate_and_acquire_ownership(cap, trec, TRUE, TRUE);
  if (result) {
    // The transaction is valid so far so we can actually start waiting.
    // (Otherwise the transaction was not valid and the thread will have to
    // retry it).

    // Put ourselves to sleep.  We retain locks on all the TVars involved
    // until we are sound asleep : (a) on the wait queues, (b) BlockedOnSTM
    // in the TSO, (c) TREC_WAITING in the Trec.  
    bloom_insert(cap, bloom_readset(trec), tso);
    
    park_tso(tso);
    trec -> state = TREC_WAITING;

    // We haven't released ownership of the transaction yet.  The TSO
    // has been put on the wait queue for the TVars it is waiting for,
    // but we haven't yet tidied up the TSO's stack and made it safe
    // to wake up the TSO.  Therefore, we must wait until the TSO is
    // safe to wake up before we release ownership - when all is well,
    // the runtime will call stmWaitUnlock() below, with the same
    // TRec.

  } else {
    unlock_stm(trec);
    free_stg_trec_header(cap, trec);
  }

  TRACE("%p : stmWait(%p)=%d", trec, tso, result);
  return result;
}


void
stmWaitUnlock(Capability *cap, StgTRecHeader *trec) {
    revert_ownership(cap, trec, TRUE);
    unlock_stm(trec);
}

/*......................................................................*/

StgBool stmReWait(Capability *cap, StgTSO *tso) {
  StgTRecHeader *trec = tso->trec;

#if defined(THREADED_RTS)
  if (XTEST()) {
    XABORT(ABORT_FALLBACK);
  }

  if (GET_INFO(UNTAG_CLOSURE((StgClosure*)trec)) == &stg_HTREC_HEADER_info)
  {
    TRACE("%p : stmReWait (htm)", trec);
    free_stg_htrec_header(cap, (StgHTRecHeader*)trec);
    return 0;
  }
#endif

  TRACE("%p : stmReWait (stm)", trec);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> enclosing_trec == NO_TREC);
  ASSERT ((trec -> state == TREC_WAITING) || 
          (trec -> state == TREC_CONDEMNED));
  
  // We must wake up.  We have already been removed from the wakeup list.

  free_stg_trec_header(cap, trec);
  return 0;
}

/*......................................................................*/

static StgClosure *read_current_value(StgTRecHeader *trec STG_UNUSED, StgTVar *tvar) {
  StgClosure *result;
  result = tvar -> current_value;

#if defined(STM_FG_LOCKS)
  while (GET_INFO(UNTAG_CLOSURE(result)) == &stg_TREC_HEADER_info) {
    TRACE("%p : read_current_value(%p) saw %p", trec, tvar, result);
    result = tvar -> current_value;
  }
#endif

  TRACE("%p : read_current_value(%p)=%p", trec, tvar, result);
  return result;
}

/*......................................................................*/

StgClosure *stmReadTVar(Capability *cap,
                        StgTRecHeader *trec, 
			StgTVar *tvar) {

#if defined(THREADED_RTS)
  // Record the write set for later wakeups.
  if (XTEST()) {
    StgHTRecHeader *htrec = (StgHTRecHeader*)trec;
    htrec -> read_set = bloom_add(htrec -> read_set, tvar);
    return tvar -> current_value;
  }
#endif


  StgTRecHeader *entry_in = NULL;
  StgClosure *result = NULL;
  TRecEntry *entry = NULL;
  TRACE("%p : stmReadTVar(%p)", trec, tvar);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> state == TREC_ACTIVE || 
          trec -> state == TREC_CONDEMNED);

  entry = get_entry_for(trec, tvar, &entry_in);

  if (entry != NULL) {
    if (entry_in == trec) {
      // Entry found in our trec
      result = entry -> new_value;
    } else {
      // Entry found in another trec
      TRecEntry *new_entry = get_new_entry(cap, trec);
      new_entry -> tvar = tvar;
      new_entry -> expected_value = entry -> expected_value;
      new_entry -> new_value = entry -> new_value;
      result = new_entry -> new_value;
    } 
  } else {
    // No entry found
    StgClosure *current_value = read_current_value(trec, tvar);
    TRecEntry *new_entry = get_new_entry(cap, trec);
    new_entry -> tvar = tvar;
    new_entry -> expected_value = current_value;
    new_entry -> new_value = current_value;
    result = current_value;
  }

  TRACE("%p : stmReadTVar(%p)=%p", trec, tvar, result);
  return result;
}

/*......................................................................*/

void stmWriteTVar(Capability *cap,
                  StgTRecHeader *trec,
		  StgTVar *tvar, 
		  StgClosure *new_value) {

#if defined(THREADED_RTS)
  // Record the write set for later wakeups.
  if (XTEST()) {
    StgHTRecHeader *htrec = (StgHTRecHeader*)trec;
    htrec -> write_set = bloom_add(htrec -> write_set, tvar);
    tvar -> current_value = new_value;
    dirty_TVAR(cap,tvar); // TODO: avoid this!
    return;
  }
#endif

  StgTRecHeader *entry_in = NULL;
  TRecEntry *entry = NULL;
  TRACE("%p : stmWriteTVar(%p, %p)", trec, tvar, new_value);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> state == TREC_ACTIVE || 
          trec -> state == TREC_CONDEMNED);

  entry = get_entry_for(trec, tvar, &entry_in);

  if (entry != NULL) {
    if (entry_in == trec) {
      // Entry found in our trec
      entry -> new_value = new_value;
    } else {
      // Entry found in another trec
      TRecEntry *new_entry = get_new_entry(cap, trec);
      new_entry -> tvar = tvar;
      new_entry -> expected_value = entry -> expected_value;
      new_entry -> new_value = new_value;
    } 
  } else {
    // No entry found
    StgClosure *current_value = read_current_value(trec, tvar);
    TRecEntry *new_entry = get_new_entry(cap, trec);
    new_entry -> tvar = tvar;
    new_entry -> expected_value = current_value;
    new_entry -> new_value = new_value;
  }

  TRACE("%p : stmWriteTVar done", trec);
}

/*......................................................................*/

// Local Variables:
// mode: C
// fill-column: 80
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
