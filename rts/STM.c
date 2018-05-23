/* -----------------------------------------------------------------------------
 * (c) The GHC Team 1998-2005
 *
 * STM implementation.
 *
 * Overview
 * --------
 *
 * See the PPoPP 2005 paper "Composable memory transactions".  In summary, each
 * transaction has a TRec (transaction record) holding entries for each of the
 * TVars (transactional variables) that it has accessed.  Each entry records (a)
 * the TVar, (b) the expected value seen in the TVar, (c) the new value that the
 * transaction wants to write to the TVar, (d) during commit, the identity of
 * the TRec that wrote the expected value.
 *
 * Separate TRecs are used for each level in a nest of transactions.  This
 * allows a nested transaction to be aborted without condemning its enclosing
 * transactions.  This is needed in the implementation of catchRetry.  Note that
 * the "expected value" in a nested transaction's TRec is the value expected to
 * be *held in memory* if the transaction commits -- not the "new value" stored
 * in one of the enclosing transactions.  This means that validation can be done
 * without searching through a nest of TRecs.
 *
 * Concurrency control
 * -------------------
 *
 * Three different concurrency control schemes can be built according to the
 * settings in STM.h:
 *
 * STM_UNIPROC assumes that the caller serialises invocations on the STM
 * interface.  In the Haskell RTS this means it is suitable only for
 * non-THREADED_RTS builds.
 *
 * STM_CG_LOCK uses coarse-grained locking -- a single 'stm lock' is acquired
 * during an invocation on the STM interface.  Note that this does not mean that
 * transactions are simply serialized -- the lock is only held *within* the
 * implementation of stmCommitTransaction, stmWait etc.
 *
 * STM_FG_LOCKS (REMOVED HERE TO MAKE THINGS SIMPILER)
 *
 * Concurrency control is implemented in the functions:
 *
 *    lock_stm/unlock_stm
 *
 * The choice between STM_UNIPROC / STM_CG_LOCK affects the
 * implementation of these functions.
 *
 * lock_stm & unlock_stm are straightforward : they acquire a simple spin-lock
 * using STM_CG_LOCK, and otherwise they are no-ops.
 *
 *
 * Using these operations, the typical pattern of a commit/validate/wait
 * operation is to (a) lock the STM, (b) lock all the TVars being updated, (c)
 * check that the TVars that were only read from still contain their expected
 * values, (d) release the locks on the TVars, writing updates to them in the
 * case of a commit, (e) unlock the STM.
 *
 * ---------------------------------------------------------------------------*/

#include "PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "Schedule.h"
#include "Stats.h"
#include "STM.h"
#include "Trace.h"
#include "Threads.h"
#include "sm/Storage.h"

#include <time.h>
#include <stdio.h>

#include "rtm-goto.h"
#include "immintrin.h"

#define TRUE 1
#define FALSE 0

/*......................................................................*/

// If SHAKE is defined then validation will sometimes spuriously fail.  They help test
// unusual code paths if genuine contention is rare

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

#define _FOR_EACH_ENTRY(_t,_x,CODE,HEADER,CHUNK,CUR,ENTRY,END_LIST,SIZE) do {   \
  __label__ exit_for_each;                                                      \
  HEADER *__t = (_t);                                                           \
  CHUNK *__c = __t -> CUR;                                            \
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
  _FOR_EACH_ENTRY(_t,_x,CODE,StgTRecHeader,StgTRecChunk,current_chunk,TRecEntry \
                 ,END_STM_CHUNK_LIST,TREC_CHUNK_NUM_ENTRIES)

#define FOR_EACH_ARRAY_ENTRY(_t,_x,CODE)                                        \
  _FOR_EACH_ENTRY(_t,_x,CODE,StgTRecHeader,StgTArrayRecChunk                    \
                  ,current_array_chunk,TArrayRecEntry                           \
                 ,END_STM_ARRAY_CHUNK_LIST,TARRAY_REC_CHUNK_NUM_ENTRIES)
/*......................................................................*/

// if REUSE_MEMORY is defined then attempt to re-use descriptors, log chunks,
// and wait queue entries without GC

#define REUSE_MEMORY

/*......................................................................*/

static void dirty_TARRAY_or_MUT_CON(Capability *cap, StgTArray *s)
{
    StgInfoTable *info = INFO_PTR_TO_STRUCT(s->header.info);
    if (info->type == MUT_CONSTR_EXT_CLEAN)
        dirty_MUT_CON_EXT(cap,(StgClosure*)s);
    else if (info->type != MUT_CONSTR_EXT_DIRTY)
        dirty_TARRAY(cap,s); // unlocking is due to a write.
}

/*......................................................................*/

#if defined(STM_UNIPROC)
static void lock_stm(Capability* cap STG_UNUSED, StgTRecHeader *trec STG_UNUSED) {
  TRACE("%p : lock_stm()", trec);
}

static void unlock_stm(Capability* cap STG_UNUSED, StgTRecHeader *trec STG_UNUSED) {
  TRACE("%p : unlock_stm()", trec);
}
#elif defined(STM_CG_LOCK) /*........................................*/
static volatile int smp_locked = 0;

// In the simple scheme, encountering a retry will cause a fallback to STM.
// We are not tracking the read set so we do not know what watch lists to
// go on.

#define HTM_LATE_LOCK_SUBSCRIPTION

static void lock_stm(Capability* cap, StgTRecHeader *trec STG_UNUSED) {
  int i,s,status;
  for (i = 0; i < RtsFlags.ConcFlags.hleRetryCount; i++)
  {
    XBEGIN(fail);
    if (smp_locked == 0)
      return;
    XEND();

    cap->stm_stats->hle_locked++;

    // spin.
    while (smp_locked != 0)
        _mm_pause(); // TODO: backoff?

    continue;
    XFAIL_STATUS(fail,status);
    cap->stm_stats->hle_fail++;

    s = status & 0xffffff;
    TRACE("%p : XFAIL %x %x %d", trec, status, s, XABORT_CODE(status));
    if ((s & XABORT_EXPLICIT) != 0) // XABORT was executed
    {
      if (XABORT_CODE(status) == ABORT_FALLBACK)
        break; // Give up and go to the fallback.

      if (XABORT_CODE(status) == ABORT_RESTART)
      { // Try again.
      }
    }
    else if ((s & XABORT_RETRY) == 0)
      break; // Hardware recommends fallback.
  }

  cap->stm_stats->hle_fallback++;

  while (__sync_lock_test_and_set(&smp_locked, 1))
  {
    while (smp_locked != 0)
      _mm_pause();
  }
  TRACE("%p : lock_stm()", trec);
}

static void unlock_stm(Capability* cap, StgTRecHeader *trec STG_UNUSED) {
  TRACE("%p : unlock_stm()", trec);
  if (smp_locked == 0)
  {
    XEND();
    cap->stm_stats->hle_commit++;
  }
  else
  {
    __sync_lock_release(&smp_locked);
    cap->stm_stats->hle_release++;
  }
}
#else
#error Usupported STM configuration.
#endif

/*......................................................................*/


/*......................................................................*/

// Helper functions for downstream allocation and initialization

static StgTRecChunk *new_stg_trec_chunk(Capability *cap) {
  StgTRecChunk *result;
  // TODO: allocateCacheAligned
  result = (StgTRecChunk *)allocate(cap, sizeofW(StgTRecChunk));
  SET_HDR (result, &stg_TREC_CHUNK_info, CCS_SYSTEM);
  result -> prev_chunk = END_STM_CHUNK_LIST;
  result -> next_entry_idx = 0;
  return result;
}

static StgTArrayRecChunk *new_stg_tarray_rec_chunk(Capability *cap) {
  StgTArrayRecChunk *result;
  // TODO: allocateCacheAligned
  result = (StgTArrayRecChunk *)allocate(cap, sizeofW(StgTArrayRecChunk));
  SET_HDR (result, &stg_TARRAY_REC_CHUNK_info, CCS_SYSTEM);
  result -> prev_chunk = END_STM_ARRAY_CHUNK_LIST;
  result -> next_entry_idx = 0;
  return result;
}

static StgTRecHeader *new_stg_trec_header(Capability *cap,
                                          StgTRecHeader *enclosing_trec) {
  StgTRecHeader *result;
  // TODO: allocateCacheAligned
  result = (StgTRecHeader *) allocate(cap, sizeofW(StgTRecHeader));
  SET_HDR (result, &stg_TREC_HEADER_info, CCS_SYSTEM);

  result -> enclosing_trec = enclosing_trec;
  result -> current_chunk = new_stg_trec_chunk(cap);
  result -> current_array_chunk = new_stg_tarray_rec_chunk(cap);
  result -> HpStart = 0;
  result -> HpEnd = 0;

  if (enclosing_trec == NO_TREC) {
    result -> state = TREC_ACTIVE;
    result -> retrying = 0;
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
  //TODO: allocateCacheAligned
  result = (StgHTRecHeader *) allocate(cap, sizeofW(StgHTRecHeader));
  SET_HDR (result, &stg_HTREC_HEADER_info, CCS_SYSTEM);

  result -> enclosing_trec = (StgHTRecHeader*)NO_TREC;
  result -> state = TREC_ACTIVE;
  result -> retrying = 0;
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

static StgTArrayRecChunk *alloc_stg_tarray_rec_chunk(Capability *cap) {
  StgTArrayRecChunk *result = NULL;
  if (cap -> free_tarray_rec_chunks == END_STM_ARRAY_CHUNK_LIST) {
    result = new_stg_tarray_rec_chunk(cap);
  } else {
    result = cap -> free_tarray_rec_chunks;
    cap -> free_tarray_rec_chunks = result -> prev_chunk;
    result -> prev_chunk = END_STM_ARRAY_CHUNK_LIST;
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

static void free_stg_tarray_rec_chunk(Capability *cap,
                                      StgTArrayRecChunk *c) {
#if defined(REUSE_MEMORY)
  c -> prev_chunk = cap -> free_tarray_rec_chunks;
  cap -> free_tarray_rec_chunks = c;
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
    result -> current_array_chunk -> next_entry_idx = 0;
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

  StgTArrayRecChunk *achunk = trec -> current_array_chunk -> prev_chunk;
  while (achunk != END_STM_ARRAY_CHUNK_LIST) {
    StgTArrayRecChunk *prev_chunk = achunk -> prev_chunk;
    free_stg_tarray_rec_chunk(cap, achunk);
    achunk = prev_chunk;
  }
  trec -> current_array_chunk -> prev_chunk = END_STM_ARRAY_CHUNK_LIST;

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

static TArrayRecEntry *get_new_array_entry(Capability *cap,
                                           StgTRecHeader *t) {
  TArrayRecEntry *result;
  StgTArrayRecChunk *c;
  int i;

  TRACE("%p : get_new_array_entry", t);

  c = t -> current_array_chunk;
  i = c -> next_entry_idx;
  ASSERT(c != END_STM_ARRAY_CHUNK_LIST);

  if (i < TARRAY_REC_CHUNK_NUM_ENTRIES) {
    // Continue to use current chunk
    result = &(c -> entries[i]);
    c -> next_entry_idx ++;
  } else {
    // Current chunk is full: allocate a fresh one
    TRACE("%p : get_new_array_entry new chunk", t);
    StgTArrayRecChunk *nc;
    nc = alloc_stg_tarray_rec_chunk(cap);
    nc -> prev_chunk = c;
    nc -> next_entry_idx = 1;
    t -> current_array_chunk = nc;
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
  int i,s,status;
  for (i = 0; i < RtsFlags.ConcFlags.hleRetryCount; i++)
  {
    XBEGIN(fail);
    if (smp_locked_bloom == 0)
      return;
    XEND();

    // spin.
    while (smp_locked_bloom != 0)
        _mm_pause(); // TODO: backoff?

    continue;
    XFAIL_STATUS(fail,status);
    // TODO: stats collection?
    s = status & 0xffffff;
    TRACE("lock_bloom : XFAIL %x %x %d", status, s, XABORT_CODE(status));
    if ((s & XABORT_EXPLICIT) != 0) // XABORT was executed
    {
      if (XABORT_CODE(status) == ABORT_FALLBACK)
        break; // Give up and go to the fallback.

      if (XABORT_CODE(status) == ABORT_RESTART)
      { // Try again.
      }
    }
    else if ((s & XABORT_RETRY) == 0)
      break; // Hardware recommends fallback.
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
#elif defined(STM_UNIPROC)
#else // !THREADED_RTS !STM_UNIPROC

static void lock_bloom(void) {
}

static void unlock_bloom(void) {
}

#endif // !THREADED_RTS

#define BLOOM_BIT_COUNT     64 // TODO: Bold assumption.

// Bloom filters for wakeups
static StgBloom bloom_add(StgBloom filter, StgWord id)
{
    return filter | id;
}

// Bloom filters for wakeups from arrays
static StgBloom bloom_add_array(StgBloom filter, StgWord array_hash, StgHalfWord index)
{
    StgWord w = filter;
    StgWord id = array_hash ^ (index << 16);

    w = w | (1 << ((id & 0x00003f0) >>  4));
    w = w | (1 << ((id & 0x003f000) >> 12));
    w = w | (1 << ((id & 0x3f00000) >> 20));

    return w;
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
// TODO: allocateCacheAligned
  result = (StgBloomWakeupChunk *)allocate(cap, sizeofW(StgBloomWakeupChunk));
  SET_HDR (result, &stg_BLOOM_WAKEUP_CHUNK_info, CCS_SYSTEM);
  result -> prev_chunk = END_BLOOM_WAKEUP_CHUNK_LIST;
  result -> next_entry_idx = 0;
  return result;
}

void markWakeupSTM (evac_fn evac, void *user)
{
    // Called durring GC so no locks are needed.
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

#ifdef THREADED_RTS
// Structure to buffer the local wakeup list as we
// take items off the global list.
typedef struct tso_wakeup_chunk_
{
    struct tso_wakeup_chunk_* prev_chunk;
    StgWord next_entry_idx;
    StgTSO* tsos[BLOOM_WAKEUP_CHUNK_NUM_ENTRIES];
} tso_wakeup_chunk;

static tso_wakeup_chunk* new_tso_wakeup_chunk(void)
{
    tso_wakeup_chunk* p = stgMallocBytes(sizeof(tso_wakeup_chunk), "tso_wakeup_chunk");
    p->next_entry_idx = 0;
    p->prev_chunk = NULL;
    return p;
}

static tso_wakeup_chunk* add_tso(tso_wakeup_chunk* chunk, StgTSO* tso)
{
    if (chunk == NULL || chunk->next_entry_idx == BLOOM_WAKEUP_CHUNK_NUM_ENTRIES)
    {
        tso_wakeup_chunk* p = new_tso_wakeup_chunk();
        p->prev_chunk = chunk;
        chunk = p;
    }

    chunk->tsos[chunk->next_entry_idx++] = tso;

    return chunk;
}

static void local_wakeup(Capability *cap, tso_wakeup_chunk* q)
{
    StgWord i;

    tso_wakeup_chunk* prev = NULL;

    for (; q != NULL; prev = q, q = q->prev_chunk)
    {
        if (prev != NULL && prev->prev_chunk != NULL) // The first chunk is stack allocated
            stgFree(prev);

        for (i = 0; i < q -> next_entry_idx; i++)
        {
            unpark_tso(cap, q->tsos[i]);
        }
    }
}
#endif

// Wake up and remove any blocked transactions who's read sets
// overlap with write sets.
static void bloom_wakeup(Capability *cap, StgBloom filter)
{
    if (filter == 0)
        return;

#ifdef THREADED_RTS
    tso_wakeup_chunk  start;
    start.prev_chunk = NULL;
    start.next_entry_idx = 0;

    tso_wakeup_chunk* tsos = &start;

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
#ifdef THREADED_RTS
                    tsos = add_tso(tsos, q -> filters[i].tso);
#else
                    // Avoid doing the wakeup here as it takes a lock.
                    unpark_tso(cap, q -> filters[i].tso);
#endif

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

    local_wakeup(cap, tsos);
#endif
}

static StgBloom bloom_readset(StgTRecHeader* trec)
{
    StgBloom filter = 0;

    FOR_EACH_ENTRY(trec, e, {
        filter = bloom_add(filter, e -> tvar -> hash_id);
    });

    FOR_EACH_ARRAY_ENTRY(trec, e, {
        filter = bloom_add_array(filter, e -> tarray -> hash_id, e -> offset);
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
#ifdef THREADED_RTS
    int htm = XTEST();

    if (htm)
    {
        // We only need to check to ensure no one takes the lock while
        // while we are in the transaction.
        StgClosure* p = (StgClosure*)tso;
        if ((P_)(void *)&p->header.info == (P_)&stg_WHITEHOLE_info)
            XABORT(ABORT_RESTART);
    }
    else
#endif
        lockTSO(tso);

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
#ifdef THREADED_RTS
    if (!htm)
#endif
        unlockTSO(tso);
}

static void unpark_waiters_on(Capability *cap, StgWord hash) {
    // We have a write, wake up any filters that include
    // the TVar being written.
    // TODO: Locking?
    bloom_wakeup(cap, hash);
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

static void merge_array_update_into(Capability *cap,
                                    StgTRecHeader *t,
                                    TArrayRecEntry *entry) {
  int found;

  // Look for an entry in this trec
  found = FALSE;
  FOR_EACH_ARRAY_ENTRY(t, e, {
    if (e -> tarray      == entry -> tarray
     && e -> offset      == entry -> offset) {
      found = TRUE;
      if (e -> expected_value.ptr != entry -> expected_value.ptr) {
        // Must abort if the two entries start from different values
        TRACE("%p : update entries inconsistent at %p (%p vs %p)",
              t, e -> tarray, e -> expected_value.ptr, entry -> expected_value.ptr);
        t -> state = TREC_CONDEMNED;
      }
      e -> new_value.ptr = entry -> new_value.ptr;
      BREAK_FOR_EACH;
    }
  });

  if (!found) {
    // No entry so far in this trec
    TArrayRecEntry *ne;
    ne = get_new_array_entry(cap, t);
    ne -> tarray             = entry -> tarray;
    ne -> offset             = entry -> offset;
    ne -> expected_value.ptr = entry -> expected_value.ptr;
    ne -> new_value.ptr      = entry -> new_value.ptr;
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

static void merge_array_read_into(Capability *cap,
                                  StgTRecHeader *trec,
                                  TArrayRecEntry *entry)
{
  int found;
  StgTRecHeader *t;

  found = FALSE;

  for (t = trec; !found && t != NO_TREC; t = t -> enclosing_trec)
  {
    FOR_EACH_ARRAY_ENTRY(t, e, {
      if ( e -> tarray      == entry -> tarray
        && e -> offset      == entry -> offset) {
        found = TRUE;
        if (e -> expected_value.ptr != entry -> expected_value.ptr) {
            // Must abort if the two entries start from different values
            TRACE("%p : read entries inconsistent at %p (%p vs %p)",
                  t, e -> tarray, e -> expected_value.ptr, entry -> expected_value.ptr);
            t -> state = TREC_CONDEMNED;
        }
        BREAK_FOR_EACH;
      }
    });
  }

  if (!found) {
    // No entry found
    TArrayRecEntry *ne;
    ne = get_new_array_entry(cap, t);
    ne -> tarray             = entry -> tarray;
    ne -> offset             = entry -> offset;
    ne -> expected_value.ptr = entry -> expected_value.ptr;
    ne -> new_value.ptr      = entry -> expected_value.ptr; // merging the read!
  }
}

/*......................................................................*/

// validate : this checks that all transactional entries match their
// in memory values.
static StgBool validate(Capability *cap STG_UNUSED, StgTRecHeader *trec) {
  StgBool result;

  if (shake()) {
    TRACE("%p : shake, pretending trec is invalid when it may not be", trec);
    return FALSE;
  }

  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_WAITING) ||
         (trec -> state == TREC_CONDEMNED));
  result = !((trec -> state) == TREC_CONDEMNED);

  // TODO: We no-longer track cap->stm_stats->validate_fail in here
  // there may be a double counting and the count might happen with
  // HLE.

#if defined(THREADED_RTS)
  // We can simply check all the values.
  if (!result)
    return FALSE;

  FOR_EACH_ENTRY(trec, e, {
    StgTVar *s;
    s = e -> tvar;
    if (s -> current_value != e -> expected_value)
      return FALSE;
  });

  FOR_EACH_ARRAY_ENTRY(trec, e, {
    StgTArray *s;
    s = e -> tarray;
    // Equality is same on .ptr as .word.
    if (s -> payload[e -> offset] != e -> expected_value.ptr)
      return FALSE;
  });
  return TRUE;
#else
  return result;
#endif
}

/************************************************************************/

void stmPreGCHook (Capability *cap) {
  lock_stm(cap, NO_TREC);
  TRACE("stmPreGCHook");
  cap->free_trec_chunks = END_STM_CHUNK_LIST;
  cap->free_tarray_rec_chunks = END_STM_ARRAY_CHUNK_LIST;
  cap->free_trec_headers = NO_TREC;
  unlock_stm(cap, NO_TREC);
}

/*......................................................................*/

#if defined(STM_UNIPROC)
StgTRecHeader *stmStartTransaction(Capability *cap,
                                   StgTRecHeader *outer) {
  StgTRecHeader *t;
  TRACE("%p : stmStartTransaction", outer);

  if (outer == NO_TREC)
  {
    cap->stm_stats->start++;
  }

  cap->stm_stats->alloc_snapshot = 0;
  t = alloc_stg_trec_header(cap, outer);
  TRACE("%p : stmStartTransaction()=%p", outer, t);
  return t;
}
#else
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

    cap->stm_stats->start++;

    TRACE("%p : stmStartTransaction()=%p XBEGIN", outer, th);
    for (i = 0; i < RtsFlags.ConcFlags.htmRetryCount; i++) {
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

      cap->stm_stats->htm_fail++;

      s = status & 0xffffff;
      TRACE("%p : XFAIL %x %x %d", outer, status, s, XABORT_CODE(status));
      if ((s & XABORT_EXPLICIT) != 0) // XABORT was executed
      {
        if (XABORT_CODE(status) == ABORT_FALLBACK)
          break; // Give up and go to the fallback.

        if (XABORT_CODE(status) == ABORT_GC)
        {
          cap->stm_stats->htm_gc++;
          break; // Give up so that GC can happen.
        }

        if (XABORT_CODE(status) == ABORT_RESTART)
        { // Try again.
        }
      }
      else if ((s & XABORT_RETRY) == 0)
        break; // Hardware recommends fallback.

      // go to fall back, system doesn't expect retry will work.
      // Perhaps our failure was due to observing the lock from a committing
      // STM transaction.  Wait until we observe the lock free.  If we do not
      // do this we risk all transactions falling back.
      while (smp_locked != 0)
          _mm_pause(); // TODO: backoff?
    }

	cap->stm_stats->htm_fallback++;

    free_stg_htrec_header(cap, th);
  }

  TRACE("%p : stmStartTransaction", outer);

  StgTRecHeader* t;
  t = alloc_stg_trec_header(cap, outer);
  TRACE("%p : stmStartTransaction()=%p", outer, t);
  return t;
}
#endif

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
  ASSERT(trec != NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_WAITING) ||
         (trec -> state == TREC_CONDEMNED));

  lock_stm(cap, trec);

  et = trec -> enclosing_trec;
  if (et == NO_TREC) {
    // We're a top-level transaction: remove any watch queue entries that
    // we may have.
    TRACE("%p : aborting top-level transaction", trec);

    cap->stm_stats->abort++;

    if (trec -> state == TREC_WAITING) {
      ASSERT(trec -> enclosing_trec == NO_TREC);
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

    FOR_EACH_ARRAY_ENTRY(trec, e, {
      merge_array_read_into(cap, et, e);
    });
  }

  trec -> state = TREC_ABORTED;
  unlock_stm(cap, trec);

  TRACE("%p : stmAbortTransaction done", trec);
}

/*......................................................................*/

void stmFreeAbortedTRec(Capability *cap,
                        StgTRecHeader *trec) {

  if (GET_INFO(UNTAG_CLOSURE((StgClosure*)trec)) != &stg_TREC_HEADER_info)
    return;

  TRACE("%p : stmFreeAbortedTRec", trec);
  ASSERT(trec != NO_TREC);
  ASSERT((trec -> state == TREC_CONDEMNED) ||
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
  ASSERT(trec != NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_WAITING) ||
         (trec -> state == TREC_CONDEMNED));

  lock_stm(cap, trec);
  if (trec -> state == TREC_WAITING) {
    ASSERT(trec -> enclosing_trec == NO_TREC);
    TRACE("%p : stmCondemnTransaction condemning waiting transaction", trec);
    // TODO: Remove read_set from filters?  We used to remove watch queue entries
    // here.
  }
  trec -> state = TREC_CONDEMNED;
  unlock_stm(cap, trec);

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

  lock_stm(cap, trec);

  t = trec;
  result = TRUE;
  while (t != NO_TREC && result) {
    result &= validate(cap, t);
    t = t -> enclosing_trec;
  }

  if (!result && trec -> state != TREC_WAITING) {
    cap->stm_stats->validate_fail++;
    trec -> state = TREC_CONDEMNED;
  }

  unlock_stm(cap, trec);

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

static TArrayRecEntry *get_array_entry_for(StgTRecHeader *trec, StgTArray *tarray,
                                           StgHalfWord access,
                                           StgHalfWord index,
                                           StgTRecHeader **in) {
  TArrayRecEntry *result = NULL;
  TRACE("%p : get_array_entry_for TArray %p[%d]", trec, tarray, index);
  ASSERT(trec != NO_TREC);

  StgWord offset = access * tarray -> ptrs + index;

  do {
    FOR_EACH_ARRAY_ENTRY(trec, e, {
      if (e -> tarray == tarray && e -> offset == offset) {
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

static int DiffHeapUse(bdescr* bs, bdescr* be, int s, int e)
{
    int total = 0;

    if (bs == be)
    {
        total = e - s;
    }
    else
    {
        total = BLOCK_SIZE*bs->blocks + s - (StgWord)bs->start;
        bs = bs->link;
        while (bs != be && bs != NULL)
        {
            total += BLOCK_SIZE*bs->blocks;
            bs = bs->link;
        }
        if (bs == NULL)
        {
           return -1;
        }
        total += e - (StgWord)be->start;
    }

    return total;
}

static double dump_gettime(void)
{
    struct timespec ts;

    clock_gettime(CLOCK_MONOTONIC, &ts);

    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void DumpTRec(Capability *cap, StgTRecHeader *trec, StgBool result, StgBool htmCommit, double time)
{
	printf("TREC: %p %d %d %0.17g\n", cap, result, htmCommit, time);
	FOR_EACH_ENTRY(trec, e, {
      printf("TVAR: %p %p %p\n", e->tvar, e->expected_value, e->new_value);
    });

    FOR_EACH_ARRAY_ENTRY(trec, e, {
	  printf("TSTR: %p %02ld 0x%lx 0x%lx\n", e->tarray, e->offset, e->expected_value.word, e->new_value.word);
    });
}

static void RecordHeapUse(Capability *cap, StgTRecHeader *trec, StgBool result, StgBool htmCommit, double time,
                          StgBool htm, StgBool read_only)
{
	if ( RtsFlags.ConcFlags.dumpTRecs )
		DumpTRec(cap, trec, result, htmCommit, time);

    // Extract how many bytes were allocated while the transaction ran.  We have
    // recorded in the trec the start Hp and end Hp.  If it was all in one block
    // we just want the difference.  If start and end are different blocks, add
    // BLOCK_SIZE for each intervening block.  Record these stats in the stm_stats
    // structure.  For STM we see aborted transactions allocations.  In HTM we don't.

    if ( trec->HpStart == 0
      || !HEAP_ALLOCED((StgPtr)trec->HpStart)
      || (((RtsFlags.ConcFlags.stmAccum/3) == 1) &&  read_only)  // Only record if wrote
      || (((RtsFlags.ConcFlags.stmAccum/3) == 2) && !read_only)) // Only record read-only
    { // We saw a GC in the life of this TREC, so no info.
        cap->stm_stats->no_record += 1;
        return;
    }

    bdescr* bs = Bdescr((StgPtr)trec->HpStart);
    bdescr* be = Bdescr((StgPtr)trec->HpEnd);

    TRACE("%p : alloc check bdescr %p -> %p, htm %d result %d, read_only %d"
          , trec, bs, be, htm, result, read_only);

    int total = DiffHeapUse(bs, be, trec->HpStart, trec->HpEnd);

    if (total < 0)
    {
        TRACE("%p : alloc failed! total %d", trec, total);
        cap->stm_stats->no_record += 1;
    }
    else
    {
        TRACE("%p : alloc total %d", trec, total);
        if (htm)
        {
            stat_stm_accum(&cap->stm_stats->htm_alloc_hp, total/8);
            stat_stm_accum(&cap->stm_stats->htm_alloc, cap->stm_stats->alloc_snapshot/8);
        }
        else
        {
            if (result)
            {
                stat_stm_accum(&cap->stm_stats->stm_alloc_committed_hp, total/8);
                stat_stm_accum(&cap->stm_stats->stm_alloc_committed, cap->stm_stats->alloc_snapshot/8);
            }
            else
            {
                stat_stm_accum(&cap->stm_stats->stm_alloc_aborted_hp, total/8);
                stat_stm_accum(&cap->stm_stats->stm_alloc_aborted, cap->stm_stats->alloc_snapshot/8);
            }
        }
    }
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
    XABORT(ABORT_RESTART);
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

  cap->stm_stats->htm_commit++;

  return TRUE;
}
#endif

/*......................................................................*/

#if defined(STM_UNIPROC)
StgBool stmCommitTransaction(Capability *cap, StgTRecHeader *trec) {
  int result;
  StgBool read_only = TRUE;

  TRACE("%p : stmCommitTransaction()", trec);
  ASSERT(trec != NO_TREC);

  double start = dump_gettime();

  lock_stm(cap, trec);

  ASSERT(trec -> enclosing_trec == NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_CONDEMNED));

  result = validate(cap, trec);
  if (result) {
    // We now know that all the updated locations hold their expected values.
    ASSERT (trec -> state == TREC_ACTIVE);

    // We now know that all of the read-only locations held their exepcted values
    // at the end of the call to validate.  This forms the
    // linearization point of the commit.

    // Make the updates required by the transaction
    FOR_EACH_ENTRY(trec, e, {
      StgTVar *s;
      s = e -> tvar;

      if (e -> new_value != e -> expected_value) {
        TRACE("%p : writing %p to %p, waking waiters", trec, e -> new_value, s);
        unpark_waiters_on(cap, s -> hash_id);
        s -> current_value = e -> new_value;
        dirty_TVAR(cap, s);
        read_only = FALSE;
      }
    });

    FOR_EACH_ARRAY_ENTRY(trec, e, {
      StgTArray *s;
      s = e -> tarray;

      if (e -> new_value.ptr != e -> expected_value.ptr) {
        // Either the entry is an update or we're not using a read phase:
        // write the value back to the TVar, unlocking it if necessary.

        TRACE("%p : writing 0x%012x to %p[%d], waking waiters, version: %ld", trec,
                      e -> new_value.ptr, s, e -> offset, s -> num_updates);
        unpark_waiters_on(cap, bloom_add_array(0, s -> hash_id, e -> offset));
        // Perform write
        s -> payload[e -> offset] = e -> new_value.ptr;
        dirty_TARRAY_or_MUT_CON(cap, s);
        read_only = FALSE;
      }
    });

    cap->stm_stats->stm_commit++;
  } else {
    cap->stm_stats->validate_fail++;
  }

  unlock_stm(cap, trec);

  RecordHeapUse(cap, trec, result, FALSE, dump_gettime() - start, FALSE, read_only);

  free_stg_trec_header(cap, trec);

  TRACE("%p : stmCommitTransaction()=%d", trec, result);

  if (!result)
    cap->stm_stats->abort++;

  return result;
}

#else // defined(STM_CG_LOCK)

StgBool stmCommitTransaction(Capability *cap, StgTRecHeader *trec) {
  int result;

  if (XTEST()) {
    return htmCommitTransaction(cap, trec);
  }

  StgBool read_only = TRUE;
  double start = dump_gettime();

  TRACE("%p : stmCommitTransaction()", trec);
  ASSERT (trec != NO_TREC);

  ASSERT (trec -> enclosing_trec == NO_TREC);
  ASSERT ((trec -> state == TREC_ACTIVE) ||
          (trec -> state == TREC_CONDEMNED));

  int i;
  for (i = 0; i < RtsFlags.ConcFlags.hleRetryCount; i++)
  {
    XBEGIN(fail);

    // Here we attempt to commit in a hardware transaction.

    FOR_EACH_ENTRY(trec, e, {
      StgTVar *s;
      s = e -> tvar;
      if (s -> current_value != e -> expected_value) // Check consistency
        XABORT(ABORT_STM_INCONSISTENT);

      if (e -> expected_value != e -> new_value)
        s -> current_value = e -> new_value; // Perform writes
    });

    FOR_EACH_ARRAY_ENTRY(trec, e, {
      StgTArray *s;
      s = e -> tarray;
      // Equality is same on .ptr as .word.
      if (s -> payload[e -> offset] != e -> expected_value.ptr)
        XABORT(ABORT_STM_INCONSISTENT);

      if (e -> expected_value.ptr != e -> new_value.ptr)
        s -> payload[e -> offset] = e -> new_value.ptr;
    });


    if (smp_locked != 0)
      XABORT(ABORT_RESTART);

    XEND(); // Commit hardware transaction.

    // Wakeup
    FOR_EACH_ENTRY(trec, e, {
      if (e -> expected_value != e -> new_value) {
        // It is only safe to do the dirty here as long as a GC can't happen between
        // the XEND and here.  We don't yield between those, so we are safe.
        dirty_TVAR(cap, e -> tvar);
        unpark_waiters_on(cap, e -> tvar -> hash_id);
      }
    });

    FOR_EACH_ARRAY_ENTRY(trec, e, {
     if (e -> expected_value.ptr != e -> new_value.ptr) {
        if (e -> offset < e -> tarray -> ptrs) // If this is a ptr access
        {
            dirty_TARRAY_or_MUT_CON(cap, e -> tarray);
        }
        unpark_waiters_on(cap, bloom_add_array(0, e -> tarray -> hash_id, e -> offset));
//        if ((((StgWord)e->tarray) & 0x3f) != 0)
//            cap->stm_stats->htm_array_unaligned++;
//        cap->stm_stats->htm_array_accesses++;
      }
    });

    cap->stm_stats->htm_commit++;
    free_stg_trec_header(cap, trec);
    return TRUE;
    // RTM Fail code path
    int status,s;
    XFAIL_STATUS(fail,status);
    cap->stm_stats->hle_fail++;

	s = status & 0xffffff;
    TRACE("%p : XFAIL %x %x %d", trec, status, s, XABORT_CODE(status));
    if ((s & XABORT_EXPLICIT) != 0) // XABORT was executed
    {
      if (XABORT_CODE(status) == ABORT_FALLBACK)
        break; // Give up and go to the fallback.

      if (XABORT_CODE(status) == ABORT_STM_INCONSISTENT)
      {
        free_stg_trec_header(cap, trec);
        return FALSE; // we are done, validation failed.
      }

      if (XABORT_CODE(status) == ABORT_RESTART)
      { // Try again, we saw the lock held.
        cap->stm_stats->hle_locked++;

        // spin.
        while (smp_locked != 0)
            _mm_pause(); // TODO: backoff?
      }
    }
    else if ((s & XABORT_RETRY) == 0)
      break; // Hardware recommends fallback.
  }

  cap->stm_stats->hle_fallback++;

  // Fallback to fully software transaction.
  while (__sync_lock_test_and_set(&smp_locked, 1))
  {
    while (smp_locked != 0)
      _mm_pause();
  }

  // Use a read-phase (i.e. don't lock TVars we've read but not updated) if
  // the configueration lets us use a read phase.

  result = validate(cap, trec);
  if (result) {
    // We now know that all the updated locations hold their expected values.
    ASSERT (trec -> state == TREC_ACTIVE);


    if (result) {
      // We now know that all of the read-only locations held their exepcted values
      // at the end of the call to validate.  This forms the
      // linearization point of the commit.

      // Make the updates required by the transaction
      FOR_EACH_ENTRY(trec, e, {
        StgTVar *s;
        s = e -> tvar;

		if (e -> new_value != e -> expected_value) {
          // Either the entry is an update or we're not using a read phase:
          // write the value back to the TVar, unlocking it if necessary.

          TRACE("%p : writing %p to %p, waking waiters", trec, e -> new_value, s);
          unpark_waiters_on(cap, s -> hash_id);
          s -> current_value = e -> new_value;
          dirty_TVAR(cap, s);
          read_only = FALSE;
        }
      });

      FOR_EACH_ARRAY_ENTRY(trec, e, {
        StgTArray *s;
        s = e -> tarray;

        if (e -> new_value.ptr != e -> expected_value.ptr) {
          // Either the entry is an update or we're not using a read phase:
          // write the value back to the TVar, unlocking it if necessary.

          TRACE("%p : writing %p to %p[%d], waking waiters", trec, e -> new_value.ptr, s, e -> offset);
          unpark_waiters_on(cap, bloom_add_array(0, s -> hash_id, e -> offset));
          // Perform write
          s -> payload[e -> offset] = e -> new_value.ptr;
          dirty_TARRAY_or_MUT_CON(cap, s);
          read_only = FALSE;
        }
      });

      cap->stm_stats->stm_commit++;
    } 
  } else {
    cap->stm_stats->validate_fail++;
  }

  unlock_stm(cap, trec);

  RecordHeapUse(cap, trec, result, FALSE, dump_gettime() - start, FALSE, read_only);

  free_stg_trec_header(cap, trec);

  TRACE("%p : stmCommitTransaction()=%d", trec, result);

  return result;
}
#endif

/*......................................................................*/

StgBool stmCommitNestedTransaction(Capability *cap, StgTRecHeader *trec) {
  StgTRecHeader *et;
  int result;

#if defined(THREADED_RTS)
  if (XTEST()) {
    return TRUE;
  }
#endif

  ASSERT(trec != NO_TREC && trec -> enclosing_trec != NO_TREC);
  TRACE("%p : stmCommitNestedTransaction() into %p", trec, trec -> enclosing_trec);
  ASSERT((trec -> state == TREC_ACTIVE) || (trec -> state == TREC_CONDEMNED));

  lock_stm(cap, trec);

  et = trec -> enclosing_trec;
  result = validate(cap, trec);
  if (result) {
    // We now know that all the updated locations hold their expected values.
    FOR_EACH_ENTRY(trec, e, {
      // Merge each entry into the enclosing transaction record.
      StgTVar *s;
      s = e -> tvar;
      merge_update_into(cap, et, s, e -> expected_value, e -> new_value);
    });

    FOR_EACH_ARRAY_ENTRY(trec, e, {
      // Merge each entry into the enclosing transaction record.
      merge_array_update_into(cap, et, e);
    });
  }
  else {
    cap->stm_stats->validate_fail++;
  }

  unlock_stm(cap, trec);

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
    XABORT(ABORT_RESTART);
  }
#endif // HTM_LATE_LOCK_SUBSCRIPTION
  // Commit the read-only transaction.
  XEND();

  // TODO: Throw an exception if `read_set` is zero.

  // We are now executing non-transactionally and have the bloom filter
  // lock.
  bloom_insert(cap, htrec -> read_set, tso);
  park_tso(tso);
  htrec -> state = TREC_WAITING;

  // We continue to hold the bloom lock until the thread can be woken.  We
  // could have a "lock" (monotonic value) per tso entry and spin on that until
  // it is ready when waking.
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
  ASSERT(trec != NO_TREC);
  ASSERT(trec -> enclosing_trec == NO_TREC);
  ASSERT((trec -> state == TREC_ACTIVE) ||
         (trec -> state == TREC_CONDEMNED));

  lock_stm(cap, trec);
  result = validate(cap, trec);
  unlock_stm(cap, trec);

  if (result) {
    // The transaction is valid so far so we can actually start waiting.
    // (Otherwise the transaction was not valid and the thread will have to
    // retry it).

    // Put ourselves to sleep.  We retain locks on all the TVars involved
    // until we are sound asleep : (a) on the wait queues, (b) BlockedOnSTM
    // in the TSO, (c) TREC_WAITING in the Trec.
#if defined(THREADED_RTS)
    lock_bloom_hle();
#endif
    bloom_insert(cap, bloom_readset(trec), tso);

    park_tso(tso);
    trec -> state = TREC_WAITING;

    // We haven't released ownership of the bloom lock yet.  The TSO
    // has been put on the wait bloom list, but we haven't yet tidied up the
    // TSO's stack and made it safe to wake up the TSO.  Therefore, we must
    // wait until the TSO is safe to wake up before we release ownership - when
    // all is well, the runtime will call stmWaitUnlock() below, with the same
    // TRec.

  } else {
    cap->stm_stats->validate_fail++;
    free_stg_trec_header(cap, trec);
  }

  TRACE("%p : stmWait(%p)=%d", trec, tso, result);
  return result;
}


void
stmWaitUnlock(Capability *cap, StgTRecHeader *trec) {
    // It is safe to unlock with the HLE version as long as every unlock is preceeded by
    // a lock.  Otherwise this is just going to make bug finding harder...
#if defined(THREADED_RTS)
    unlock_bloom_hle();
#endif

    if (trec->retrying != 0)
        cap->stm_stats->failed_wakeup++;
    else
        cap->stm_stats->retry++;
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
  ASSERT(trec != NO_TREC);
  ASSERT(trec -> enclosing_trec == NO_TREC);
  ASSERT((trec -> state == TREC_WAITING) ||
         (trec -> state == TREC_CONDEMNED));

  // We must wake up.  We have already been removed from the wakeup list.

  free_stg_trec_header(cap, trec);
  return 0;
}

/*......................................................................*/

static StgClosure *read_current_value(StgTRecHeader *trec STG_UNUSED, StgTVar *tvar) {
  StgClosure *result;
  result = tvar -> current_value;

  TRACE("%p : read_current_value(%p)=%p", trec, tvar, result);
  return result;
}

static StgClosure *read_array_current_value(StgTRecHeader *trec STG_UNUSED,
                                            StgTArray *tarray,
                                            StgHalfWord index) {

  ASSERT (index < tarray -> ptrs);

  StgClosure *result;
  result = (StgClosure*)tarray -> payload[index];
  // TODO: bounds check?
  // TODO: Fence?

  TRACE("%p : read_array_current_value(%p[%d])=%p", trec, tarray, index, result);
  return result;
}

/*......................................................................*/

static StgWord read_array_current_value_word(StgTRecHeader *trec STG_UNUSED,
                                             StgTArray *tarray,
                                             StgHalfWord index) {
  ASSERT (index < tarray -> words);

  StgWord result;
  result = (StgWord)(tarray -> payload[tarray -> ptrs + index]);
  // TODO: bounds check?
  // TODO: Fence?

  TRACE("%p : read_array_current_value_word(%p[%d])=%ld", trec, tarray, index, result);
  return result;
}

/*......................................................................*/

StgClosure *stmReadTVar(Capability *cap,
                        StgTRecHeader *trec,
                        StgTVar *tvar) {
  StgTRecHeader *entry_in = NULL;
  StgClosure *result = NULL;
  TRecEntry *entry = NULL;
  TRACE("%p : stmReadTVar(%p)", trec, tvar);
  ASSERT(trec != NO_TREC);
  ASSERT(trec -> state == TREC_ACTIVE ||
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

  StgTRecHeader *entry_in = NULL;
  TRecEntry *entry = NULL;
  TRACE("%p : stmWriteTVar(%p, %p)", trec, tvar, new_value);
  ASSERT(trec != NO_TREC);
  ASSERT(trec -> state == TREC_ACTIVE ||
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

void stmInitMutCon(StgClosure* obj) {
    StgTArray *tarray = (StgTArray*)UNTAG_CLOSURE(obj);
    const StgInfoTable *info = get_itbl((StgClosure*)tarray);

    tarray -> lock    = 0;
    tarray -> hash_id = (StgWord)obj;
    tarray -> ptrs    = info->layout.payload.ptrs;
    tarray -> words   = info->layout.payload.nptrs;

    TRACE("%p : stmInitMutCon", tarray);
}

/*......................................................................*/

void stmDebugTRefIndex(StgWord a,
                        StgWord b,
                        StgWord c,
                        StgClosure* tarrayCmm,
                        StgWord     indexCmm,
                        StgClosure* obj,
                        StgWord     pre_tag_index) {
  StgTArray *tarray = (StgTArray*)UNTAG_CLOSURE(obj);
  StgWord index = ((((StgWord)obj) + pre_tag_index) - (StgWord)(tarray -> payload))/sizeof(StgWord);

  ASSERT (tarray == tarrayCmm);
  ASSERT (index  == indexCmm);

  if (tarray != tarrayCmm) {
    barf("TRef cmm untagging wrong.");
  }
  if (index != indexCmm) {
    barf("TRef cmm indexing wrong.");
  }
}

StgClosure *stmReadTRef(Capability *cap,
                        StgTRecHeader *trec,
                        StgClosure* obj,
                        StgWord pre_tag_index) {

  StgTArray *tarray = (StgTArray*)UNTAG_CLOSURE(obj);
  StgWord index = ((((StgWord)obj) + pre_tag_index) - (StgWord)(tarray -> payload))/sizeof(StgWord);
  StgTRecHeader *entry_in = NULL;
  StgClosure *result = NULL;
  TArrayRecEntry *entry = NULL;
  TRACE("%p : stmReadTRef(%p[%d])", trec, tarray, index);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> state == TREC_ACTIVE ||
          trec -> state == TREC_CONDEMNED);

  entry = get_array_entry_for(trec, tarray, 0, index, &entry_in);

  if (entry != NULL) {
    if (entry_in == trec) {
      // Entry found in our trec
      result = entry -> new_value.ptr;
    } else {
      // Entry found in another trec
      TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
      TRACE("%p : stmReadTRef copied from %p", trec, entry_in);
      new_entry -> tarray = tarray;
      new_entry -> offset = index;
      new_entry -> expected_value.ptr = entry -> expected_value.ptr;
      new_entry -> new_value.ptr = entry -> new_value.ptr;
      result = new_entry -> new_value.ptr;
    }
  } else {
    // No entry found
    StgClosure *current_value = read_array_current_value(trec, tarray, index);
    TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
    TRACE("%p : stmReadTRef new entry with value %p", trec, current_value);
    new_entry -> tarray = tarray;
    new_entry -> offset = index;
    new_entry -> expected_value.ptr = current_value;
    new_entry -> new_value.ptr = current_value;
    result = current_value;
  }

  TRACE("%p : stmReadTRef(%p[%d])=%p", trec, tarray, index, result);
  return result;
}

/*......................................................................*/

void stmWriteTRef(Capability *cap,
                  StgTRecHeader *trec,
                  StgClosure *obj,
                  StgWord pre_tag_index,
                  StgClosure *new_value) {

  StgTArray *tarray = (StgTArray*)UNTAG_CLOSURE(obj);
  // TODO: improve this code by using this representation more directly
  // instead of reusing the existing get_array_entry_for.
  StgWord index = ((((StgWord)obj) + pre_tag_index) - (StgWord)(tarray -> payload))/sizeof(StgWord);
  // StgWord index = (pre_tag_index + tag - sizeof(StgTArray)) / 8;
  StgTRecHeader *entry_in = NULL;
  TArrayRecEntry *entry = NULL;
  TRACE("%p : stmWriteTRef(%p[%d], %p)", trec, tarray, index, new_value);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> state == TREC_ACTIVE ||
          trec -> state == TREC_CONDEMNED);

  entry = get_array_entry_for(trec, tarray, 0, index, &entry_in);

  if (entry != NULL) {
    if (entry_in == trec) {
      // Entry found in our trec
      entry -> new_value.ptr = new_value;
    } else {
      // Entry found in another trec
      TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
      new_entry -> tarray = tarray;
      new_entry -> offset = index;
      new_entry -> expected_value.ptr = entry -> expected_value.ptr;
      new_entry -> new_value.ptr = new_value;
    }
  } else {
    // No entry found
    StgClosure *current_value = read_array_current_value(trec, tarray, index);
    TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
    new_entry -> tarray = tarray;
    new_entry -> offset = index;
    new_entry -> expected_value.ptr = current_value;
    new_entry -> new_value.ptr = new_value;
  }

  TRACE("%p : stmWriteTRef done", trec);
}/*......................................................................*/



/*......................................................................*/

StgClosure *stmReadTArray(Capability *cap,
                        StgTRecHeader *trec,
                        StgTArray *tarray,
                        StgHalfWord index) {

  StgTRecHeader *entry_in = NULL;
  StgClosure *result = NULL;
  TArrayRecEntry *entry = NULL;
  TRACE("%p : stmReadTArray(%p[%d])", trec, tarray, index);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> state == TREC_ACTIVE ||
          trec -> state == TREC_CONDEMNED);

  entry = get_array_entry_for(trec, tarray, 0, index, &entry_in);

  if (entry != NULL) {
    if (entry_in == trec) {
      // Entry found in our trec
      result = entry -> new_value.ptr;
    } else {
      // Entry found in another trec
      TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
      TRACE("%p : stmReadTArray copied from %p", trec, entry_in);
      new_entry -> tarray = tarray;
      new_entry -> offset = index;
      new_entry -> expected_value.ptr = entry -> expected_value.ptr;
      new_entry -> new_value.ptr = entry -> new_value.ptr;
      result = new_entry -> new_value.ptr;
    }
  } else {
    // No entry found
    StgClosure *current_value = read_array_current_value(trec, tarray, index);
    TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
    TRACE("%p : stmReadTArray new entry with value %p", trec, current_value);
    new_entry -> tarray = tarray;
    new_entry -> offset = index;
    new_entry -> expected_value.ptr = current_value;
    new_entry -> new_value.ptr = current_value;
    result = current_value;
  }

  TRACE("%p : stmReadTArray(%p[%d])=%p", trec, tarray, index, result);
  return result;
}

/*......................................................................*/

void stmWriteTArray(Capability *cap,
                    StgTRecHeader *trec,
                    StgTArray *tarray,
                    StgHalfWord index,
                    StgClosure *new_value) {

  StgTRecHeader *entry_in = NULL;
  TArrayRecEntry *entry = NULL;
  TRACE("%p : stmWriteTArray(%p[%d], %p)", trec, tarray, index, new_value);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> state == TREC_ACTIVE ||
          trec -> state == TREC_CONDEMNED);

  entry = get_array_entry_for(trec, tarray, 0, index, &entry_in);

  if (entry != NULL) {
    if (entry_in == trec) {
      // Entry found in our trec
      entry -> new_value.ptr = new_value;
    } else {
      // Entry found in another trec
      TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
      new_entry -> tarray = tarray;
      new_entry -> offset = index;
      new_entry -> expected_value.ptr = entry -> expected_value.ptr;
      new_entry -> new_value.ptr = new_value;
    }
  } else {
    // No entry found
    StgClosure *current_value = read_array_current_value(trec, tarray, index);
    TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
    new_entry -> tarray = tarray;
    new_entry -> offset = index;
    new_entry -> expected_value.ptr = current_value;
    new_entry -> new_value.ptr = new_value;
  }

  TRACE("%p : stmWriteTVar done", trec);
}/*......................................................................*/

StgWord stmReadTArrayWord(Capability *cap,
                          StgTRecHeader *trec,
                          StgTArray *tarray,
                          StgHalfWord index) {

  StgTRecHeader *entry_in = NULL;
  StgWord result = 0;
  TArrayRecEntry *entry = NULL;
  TRACE("%p : stmReadTArrayWord(%p[%d])", trec, tarray, index);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> state == TREC_ACTIVE ||
          trec -> state == TREC_CONDEMNED);

  entry = get_array_entry_for(trec, tarray, 1, index, &entry_in);

  if (entry != NULL) {
    if (entry_in == trec) {
      // Entry found in our trec
      result = entry -> new_value.word;
    } else {
      // Entry found in another trec
      TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
      new_entry -> tarray = tarray;
      new_entry -> offset = tarray -> ptrs + index;
      new_entry -> expected_value.word = entry -> expected_value.word;
      new_entry -> new_value.word = entry -> new_value.word;
      result = new_entry -> new_value.word;
    }
  } else {
    // No entry found
    StgWord current_value = read_array_current_value_word(trec, tarray, index);
    TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
    new_entry -> tarray = tarray;
    new_entry -> offset = tarray -> ptrs + index;
    new_entry -> expected_value.word = current_value;
    new_entry -> new_value.word = current_value;
    result = current_value;
  }

  TRACE("%p : stmReadTArrayWord(%p[%d])=%ld", trec, tarray, index, result);
  return result;
}

/*......................................................................*/

void stmWriteTArrayWord(Capability *cap,
                        StgTRecHeader *trec,
                        StgTArray *tarray,
                        StgHalfWord index,
                        StgWord new_value) {

  StgTRecHeader *entry_in = NULL;
  TArrayRecEntry *entry = NULL;
  TRACE("%p : stmWriteTArrayWord(%p[%d], %p)", trec, tarray, index, new_value);
  ASSERT (trec != NO_TREC);
  ASSERT (trec -> state == TREC_ACTIVE ||
          trec -> state == TREC_CONDEMNED);

  entry = get_array_entry_for(trec, tarray, 1, index, &entry_in);

  if (entry != NULL) {
    if (entry_in == trec) {
      // Entry found in our trec
      entry -> new_value.word = new_value;
    } else {
      // Entry found in another trec
      TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
      new_entry -> tarray = tarray;
      new_entry -> offset = tarray -> ptrs + index;
      new_entry -> expected_value.word = entry -> expected_value.word;
      new_entry -> new_value.word = new_value;
    }
  } else {
    // No entry found
    StgWord current_value = read_array_current_value_word(trec, tarray, index);
    TArrayRecEntry *new_entry = get_new_array_entry(cap, trec);
    new_entry -> tarray = tarray;
    new_entry -> offset = tarray -> ptrs + index;
    new_entry -> expected_value.word = current_value;
    new_entry -> new_value.word = new_value;
  }

  TRACE("%p : stmWriteTVar done", trec);
}

/*......................................................................*/

