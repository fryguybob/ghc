/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2005
 *
 * Statistics and timing-related functions.
 *
 * ---------------------------------------------------------------------------*/

#include "PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "Schedule.h"
#include "Stats.h"
#include "Profiling.h"
#include "GetTime.h"
#include "sm/Storage.h"
#include "sm/GC.h" // gc_alloc_block_sync, whitehole_spin
#include "sm/GCThread.h"
#include "sm/BlockAlloc.h"

#if defined(THREADED_RTS)
#include "immintrin.h"
#endif

#if USE_PAPI
#include "Papi.h"
#endif

/* huh? */
#define BIG_STRING_LEN              512

#define TimeToSecondsDbl(t) ((double)(t) / TIME_RESOLUTION)

static Time
    start_init_cpu, start_init_elapsed,
    end_init_cpu,   end_init_elapsed,
    start_exit_cpu, start_exit_elapsed,
    end_exit_cpu,   end_exit_elapsed;

static Time GC_tot_cpu  = 0;

static StgWord64 GC_tot_alloc      = 0;
static StgWord64 GC_tot_copied     = 0;

static StgWord64 GC_par_max_copied = 0;
static StgWord64 GC_par_tot_copied = 0;

#ifdef PROFILING
static Time RP_start_time  = 0, RP_tot_time  = 0;  // retainer prof user time
static Time RPe_start_time = 0, RPe_tot_time = 0;  // retainer prof elap time

static Time HC_start_time, HC_tot_time = 0;     // heap census prof user time
static Time HCe_start_time, HCe_tot_time = 0;   // heap census prof elap time
#endif

#ifdef PROFILING
#define PROF_VAL(x)   (x)
#else
#define PROF_VAL(x)   0
#endif

// current = current as of last GC
static W_ current_residency = 0; // in words; for stats only
static W_ max_residency     = 0;
static W_ cumulative_residency = 0;
static W_ residency_samples = 0; // for stats only
static W_ current_slop      = 0;
static W_ max_slop          = 0;

static W_ GC_end_faults = 0;

static Time *GC_coll_cpu = NULL;
static Time *GC_coll_elapsed = NULL;
static Time *GC_coll_max_pause = NULL;

static void statsFlush( void );
static void statsClose( void );

/* -----------------------------------------------------------------------------
   STM stats
   ------------------------------------------------------------------------- */

#if defined(THREADED_RTS)
static volatile int smp_locked_stm_stats = 0;

static void lock_stm_stats(void) {
  while (__sync_lock_test_and_set(&smp_locked_stm_stats, 1))
  {
    while (smp_locked_stm_stats != 0)
      _mm_pause();
  }
}

static void unlock_stm_stats(void) {
    __sync_lock_release(&smp_locked_stm_stats);
}
#else
static void lock_stm_stats(void) {}
static void unlock_stm_stats(void) {}
#endif

// protected by the stm_stats lock
static stm_stats_node *smp_stm_stats = NULL;

static void initSTMStatsValues(stm_stats* s)
{
    s->start = 0;
    s->abort = 0;
    s->retry = 0;
    s->validate_fail = 0;
    s->failed_wakeup = 0;

    s->stm_commit = 0;
    s->htm_commit = 0;
    s->htm_fallback = 0;
    s->htm_fail = 0;
    s->htm_gc = 0;

    s->hle_locked = 0;
    s->hle_fail = 0;
    s->hle_fallback = 0;
    s->hle_commit = 0;
    s->hle_release = 0;

    s->htm_array_unaligned = 0;
    s->htm_array_accesses = 0;

    nat init = RtsFlags.ConcFlags.stmAccum == 2 ? 0xffffffff : 0;
    s->htm_alloc_hp = init;
    s->htm_alloc = init;
    s->stm_alloc_committed_hp = init;
    s->stm_alloc_committed = init;
    s->stm_alloc_aborted_hp = init;
    s->stm_alloc_aborted = init;
    s->no_record = 0;
}

void stat_stm_accum(nat* w, nat v)
{
    switch (RtsFlags.ConcFlags.stmAccum)
    {
        default:
        case 0: *w += v;              break; // SUM
        case 1: *w = v > *w ? v : *w; break; // MAX
        case 2: *w = v < *w ? v : *w; break; // MIN
    }
}

static void addSTMStats(stm_stats* acc, stm_stats* s)
{
    acc->start += s->start;
    acc->abort += s->abort;
    acc->retry += s->retry;
    acc->validate_fail += s->validate_fail;
    acc->failed_wakeup += s->failed_wakeup;

    acc->stm_commit += s->stm_commit;
    acc->htm_commit += s->htm_commit;
    acc->htm_fallback += s->htm_fallback;
    acc->htm_fail += s->htm_fail;
    acc->htm_gc += s->htm_gc;

    acc->hle_locked   += s->hle_locked;
    acc->hle_fail     += s->hle_fail;
    acc->hle_fallback += s->hle_fallback;
    acc->hle_commit   += s->hle_commit;
    acc->hle_release  += s->hle_release;

    acc->htm_array_unaligned += s->htm_array_unaligned;
    acc->htm_array_accesses  += s->htm_array_accesses;

    stat_stm_accum(&acc->htm_alloc_hp,           s->htm_alloc_hp);
    stat_stm_accum(&acc->htm_alloc,              s->htm_alloc);
    stat_stm_accum(&acc->stm_alloc_committed_hp, s->stm_alloc_committed_hp);
    stat_stm_accum(&acc->stm_alloc_committed,    s->stm_alloc_committed);
    stat_stm_accum(&acc->stm_alloc_aborted_hp,   s->stm_alloc_aborted_hp);
    stat_stm_accum(&acc->stm_alloc_aborted,      s->stm_alloc_aborted);
    stat_stm_accum(&acc->no_record,              s->no_record);
}

static void printSTMStats(stm_stats* s)
{
    char temp[BIG_STRING_LEN];

    showStgWord64(s->start,         temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->abort,         temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->retry,         temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->validate_fail, temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->failed_wakeup, temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->stm_commit,    temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->htm_commit,    temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->stm_alloc_committed_hp, temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->stm_alloc_committed, temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->stm_alloc_aborted_hp,temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->stm_alloc_aborted,   temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->no_record,     temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
}

static void printHTMStats(stm_stats* s)
{
    char temp[BIG_STRING_LEN];

    showStgWord64(s->htm_fallback,  temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->htm_gc,        temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->htm_fail,      temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->hle_locked,    temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->hle_fail,      temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->hle_fallback,  temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->hle_commit,    temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->hle_release,   temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->htm_array_unaligned, temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->htm_array_accesses,  temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->htm_alloc_hp,  temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
    showStgWord64(s->htm_alloc,     temp, rtsTrue/*commas*/);
    statsPrintf("%16s ", temp);
}

static void printTMSizes(void)
{
    char temp[BIG_STRING_LEN];

    debugBelch("Sizes:\n"

               "TVar         "
               "TStruct      "

               "TRecHeader   "
               "HTRecHeader  "

               "TRecChunk    "
               "Entries      "
               "Entry        "

               "ArrChunk     "
               "Entries      "
               "Entry        "

               "BloomChunk   "
               "Entries      "
               "Entry        "
               "\n");

    showStgWord64(sizeof(StgTVar),          temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);
    showStgWord64(sizeof(StgStmMutArrPtrs), temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);

    showStgWord64(sizeof(StgTRecHeader),   temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);
    showStgWord64(sizeof(StgHTRecHeader),  temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);

    showStgWord64(sizeof(StgTRecChunk),    temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);
    showStgWord64(TREC_CHUNK_NUM_ENTRIES,  temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);
    showStgWord64(sizeof(TRecEntry),       temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);

    showStgWord64(sizeof(StgTArrayRecChunk),    temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);
    showStgWord64(TARRAY_REC_CHUNK_NUM_ENTRIES, temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);
    showStgWord64(sizeof(TArrayRecEntry),       temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);

    showStgWord64(sizeof(StgBloomWakeupChunk),    temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);
    showStgWord64(BLOOM_WAKEUP_CHUNK_NUM_ENTRIES, temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);
    showStgWord64(sizeof(BloomWakeupEntry),       temp, rtsTrue/*commas*/); statsPrintf("%12s ", temp);

    debugBelch("\n");
}


static void printTMAllocStats(stm_stats* s)
{
    double t;
    switch (RtsFlags.ConcFlags.stmAccum) // AVE
    {
    default:
    case 0: // AVE
        t = s->stm_commit - s->no_record;
        statsPrintf("STM-committed: Hp-alloc %10.0lf, allocate %10.0lf, both %10.0lf ave %4d%%\n"
                   , (double)s->stm_alloc_committed_hp / t
                   , (double)s->stm_alloc_committed    / t
                   , ((double)s->stm_alloc_committed_hp+(double)s->stm_alloc_committed) / t
                   , (int)((double)s->stm_commit*100.0/((double)s->htm_commit+(double)s->stm_commit)));
        statsPrintf("STM-aborted  : Hp-alloc %10.0lf, allocate %10.0lf, both %10.0lf ave\n"
                   , (double)s->stm_alloc_aborted_hp / (double)s->abort
                   , (double)s->stm_alloc_aborted    / (double)s->abort
                   , ((double)s->stm_alloc_aborted_hp+(double)s->stm_alloc_aborted)
                        / (double)s->abort);
        statsPrintf("HTM          : Hp-alloc %10.0lf, allocate %10.0lf, both %10.0lf ave %4d%%\n"
                   , (double)s->htm_alloc_hp / (double)s->htm_commit
                   , (double)s->htm_alloc    / (double)s->htm_commit
                   , ((double)s->htm_alloc_hp + (double)s->htm_alloc) / (double)s->htm_commit
                   , (int)((double)s->htm_commit*100.0/((double)s->htm_commit+(double)s->stm_commit)));
        break;
    case 1: // MAX
        statsPrintf("STM-committed: Hp-alloc %10d, allocate %10d, both %10d max\n"
                   , s->stm_alloc_committed_hp , s->stm_alloc_committed
                   , s->stm_alloc_committed_hp + s->stm_alloc_committed);
        statsPrintf("STM-aborted  : Hp-alloc %10d, allocate %10d, both %10d max\n"
                   , s->stm_alloc_aborted_hp , s->stm_alloc_aborted
                   , s->stm_alloc_aborted_hp + s->stm_alloc_aborted);
        statsPrintf("HTM          : Hp-alloc %10d, allocate %10d, both %10d max\n"
                   , s->htm_alloc_hp , s->htm_alloc
                   , s->htm_alloc_hp + s->htm_alloc);
        break;
    case 2: // MIN
        statsPrintf("STM-committed: Hp-alloc %10d, allocate %10d, both %10d min\n"
                   , s->stm_alloc_committed_hp , s->stm_alloc_committed
                   , s->stm_alloc_committed_hp + s->stm_alloc_committed);
        statsPrintf("STM-aborted  : Hp-alloc %10d, allocate %10d, both %10d min\n"
                   , s->stm_alloc_aborted_hp , s->stm_alloc_aborted
                   , s->stm_alloc_aborted_hp + s->stm_alloc_aborted);
        statsPrintf("HTM          : Hp-alloc %10d, allocate %10d, both %10d min\n"
                   , s->htm_alloc_hp , s->htm_alloc
                   , s->htm_alloc_hp + s->htm_alloc);
        break;
    }

    debugBelch("\n");
}

void initSTMStats(Capability* cap)
{
    stm_stats_node* node = (stm_stats_node*)stgMallocBytes(
        sizeof(stm_stats_node),"initSTMStats");

    node->next = NULL;
    node->cap_no = cap->no;

    initSTMStatsValues(&node->stats);

    cap->stm_stats = &node->stats;

    lock_stm_stats();

    node->next = smp_stm_stats;
    smp_stm_stats = node;

    unlock_stm_stats();
}

/* -----------------------------------------------------------------------------
   Current elapsed time
   ------------------------------------------------------------------------- */

Time stat_getElapsedTime(void)
{
    return getProcessElapsedTime() - start_init_elapsed;
}

/* ---------------------------------------------------------------------------
   Measure the current MUT time, for profiling
   ------------------------------------------------------------------------ */

double
mut_user_time_until( Time t )
{
    return TimeToSecondsDbl(t - GC_tot_cpu);
    // heapCensus() time is included in GC_tot_cpu, so we don't need
    // to subtract it here.
}

double
mut_user_time( void )
{
    Time cpu;
    cpu = getProcessCPUTime();
    return mut_user_time_until(cpu);
}

#ifdef PROFILING
/*
  mut_user_time_during_RP() returns the MUT time during retainer profiling.
  The same is for mut_user_time_during_HC();
 */
double
mut_user_time_during_RP( void )
{
    return TimeToSecondsDbl(RP_start_time - GC_tot_cpu - RP_tot_time);
}

double
mut_user_time_during_heap_census( void )
{
    return TimeToSecondsDbl(HC_start_time - GC_tot_cpu - RP_tot_time);
}
#endif /* PROFILING */

/* ---------------------------------------------------------------------------
   initStats0() has no dependencies, it can be called right at the beginning
   ------------------------------------------------------------------------ */

void
initStats0(void)
{
    start_init_cpu    = 0;
    start_init_elapsed = 0;
    end_init_cpu     = 0;
    end_init_elapsed  = 0;

    start_exit_cpu    = 0;
    start_exit_elapsed = 0;
    end_exit_cpu     = 0;
    end_exit_elapsed  = 0;

    GC_tot_alloc     = 0;
    GC_tot_copied    = 0;
    GC_par_max_copied = 0;
    GC_par_tot_copied = 0;
    GC_tot_cpu  = 0;

#ifdef PROFILING
    RP_start_time  = 0;
    RP_tot_time  = 0;
    RPe_start_time = 0;
    RPe_tot_time = 0;

    HC_start_time = 0;
    HC_tot_time = 0;
    HCe_start_time = 0;
    HCe_tot_time = 0;
#endif

    max_residency = 0;
    cumulative_residency = 0;
    residency_samples = 0;
    max_slop = 0;

    GC_end_faults = 0;
}    

/* ---------------------------------------------------------------------------
   initStats1() can be called after setupRtsFlags()
   ------------------------------------------------------------------------ */

void
initStats1 (void)
{
    nat i;
  
    if (RtsFlags.GcFlags.giveStats >= VERBOSE_GC_STATS) {
        statsPrintf("    Alloc    Copied     Live     GC     GC      TOT      TOT  Page Flts\n");
        statsPrintf("    bytes     bytes     bytes   user   elap     user     elap\n");
    }
    GC_coll_cpu = 
	(Time *)stgMallocBytes(
            sizeof(Time)*RtsFlags.GcFlags.generations,
	    "initStats");
    GC_coll_elapsed = 
	(Time *)stgMallocBytes(
	    sizeof(Time)*RtsFlags.GcFlags.generations,
	    "initStats");
    GC_coll_max_pause =
	(Time *)stgMallocBytes(
	    sizeof(Time)*RtsFlags.GcFlags.generations,
	    "initStats");
    for (i = 0; i < RtsFlags.GcFlags.generations; i++) {
	GC_coll_cpu[i] = 0;
        GC_coll_elapsed[i] = 0;
        GC_coll_max_pause[i] = 0;
    }
}

/* -----------------------------------------------------------------------------
   Initialisation time...
   -------------------------------------------------------------------------- */

void
stat_startInit(void)
{
    getProcessTimes(&start_init_cpu, &start_init_elapsed);
}

void 
stat_endInit(void)
{
    getProcessTimes(&end_init_cpu, &end_init_elapsed);

#if USE_PAPI
    /* We start counting events for the mutator
     * when garbage collection starts
     * we switch to the GC event set. */
    papi_start_mutator_count();

    /* This flag is needed to avoid counting the last GC */
    papi_is_reporting = 1;

#endif
}

/* -----------------------------------------------------------------------------
   stat_startExit and stat_endExit
   
   These two measure the time taken in shutdownHaskell().
   -------------------------------------------------------------------------- */

void
stat_startExit(void)
{
    getProcessTimes(&start_exit_cpu, &start_exit_elapsed);

#if USE_PAPI
    /* We stop counting mutator events
     * GC events are not being counted at this point */
    papi_stop_mutator_count();

    /* This flag is needed, because GC is run once more after this function */
    papi_is_reporting = 0;
#endif
}

void
stat_endExit(void)
{
    getProcessTimes(&end_exit_cpu, &end_exit_elapsed);
}

/* -----------------------------------------------------------------------------
   Called at the beginning of each GC
   -------------------------------------------------------------------------- */

static nat rub_bell = 0;

void
stat_startGC (Capability *cap, gc_thread *gct)
{
    nat bell = RtsFlags.GcFlags.ringBell;

    if (bell) {
	if (bell > 1) {
	    debugBelch(" GC ");
	    rub_bell = 1;
	} else {
	    debugBelch("\007");
	}
    }

#if USE_PAPI
    if(papi_is_reporting) {
      /* Switch to counting GC events */
      papi_stop_mutator_count();
      papi_start_gc_count();
    }
#endif

    getProcessTimes(&gct->gc_start_cpu, &gct->gc_start_elapsed);

    // Post EVENT_GC_START with the same timestamp as used for stats
    // (though converted from Time=StgInt64 to EventTimestamp=StgWord64).
    // Here, as opposed to other places, the event is emitted on the cap
    // that initiates the GC and external tools expect it to have the same
    // timestamp as used in +RTS -s calculcations.
    traceEventGcStartAtT(cap,
                         TimeToNS(gct->gc_start_elapsed - start_init_elapsed));

    if (RtsFlags.GcFlags.giveStats != NO_GC_STATS)
    {
        gct->gc_start_faults = getPageFaults();
    }
}

/* -----------------------------------------------------------------------------
 * Calculate the total allocated memory since the start of the
 * program.  Also emits events reporting the per-cap allocation
 * totals.
 * -------------------------------------------------------------------------- */

static StgWord
calcTotalAllocated(void)
{
    W_ tot_alloc = 0;
    W_ n;
    for (n = 0; n < n_capabilities; n++) {
        tot_alloc += capabilities[n]->total_allocated;
        traceEventHeapAllocated(capabilities[n],
                                CAPSET_HEAP_DEFAULT,
                                capabilities[n]->total_allocated * sizeof(W_));
    }

    return tot_alloc;
}

/* -----------------------------------------------------------------------------
   Called at the end of each GC
   -------------------------------------------------------------------------- */

void
stat_endGC (Capability *cap, gc_thread *gct,
            W_ live, W_ copied, W_ slop, nat gen,
            nat par_n_threads, W_ par_max_copied, W_ par_tot_copied)
{
    W_ tot_alloc;
    W_ alloc;

    if (RtsFlags.GcFlags.giveStats != NO_GC_STATS ||
        RtsFlags.ProfFlags.doHeapProfile)
        // heap profiling needs GC_tot_time
    {
        Time cpu, elapsed, gc_cpu, gc_elapsed;

        // Has to be emitted while all caps stopped for GC, but before GC_END.
        // See trac.haskell.org/ThreadScope/wiki/RTSsummaryEvents
        // for a detailed design rationale of the current setup
        // of GC eventlog events.
        traceEventGcGlobalSync(cap);
	
        // Emitted before GC_END on all caps, which simplifies tools code.
        traceEventGcStats(cap,
                          CAPSET_HEAP_DEFAULT,
                          gen,
                          copied * sizeof(W_),
                          slop   * sizeof(W_),
                          /* current loss due to fragmentation */
                          (mblocks_allocated * BLOCKS_PER_MBLOCK - n_alloc_blocks)
                                 * BLOCK_SIZE_W * sizeof(W_),
                          par_n_threads,
                          par_max_copied * sizeof(W_),
                          par_tot_copied * sizeof(W_));

        getProcessTimes(&cpu, &elapsed);

        // Post EVENT_GC_END with the same timestamp as used for stats
        // (though converted from Time=StgInt64 to EventTimestamp=StgWord64).
        // Here, as opposed to other places, the event is emitted on the cap
        // that initiates the GC and external tools expect it to have the same
        // timestamp as used in +RTS -s calculcations.
        traceEventGcEndAtT(cap, TimeToNS(elapsed - start_init_elapsed));

        gc_elapsed = elapsed - gct->gc_start_elapsed;
        gc_cpu = cpu - gct->gc_start_cpu;

        /* For the moment we calculate both per-HEC and total allocation.
	 * There is thus redundancy here, but for the moment we will calculate
	 * it both the old and new way and assert they're the same.
	 * When we're sure it's working OK then we can simplify things.
         */
        tot_alloc = calcTotalAllocated();

        // allocated since the last GC
        alloc = tot_alloc - GC_tot_alloc;
        GC_tot_alloc = tot_alloc;

        if (RtsFlags.GcFlags.giveStats == VERBOSE_GC_STATS) {
	    W_ faults = getPageFaults();
	    
	    statsPrintf("%9" FMT_SizeT " %9" FMT_SizeT " %9" FMT_SizeT,
		    alloc*sizeof(W_), copied*sizeof(W_), 
			live*sizeof(W_));
            statsPrintf(" %6.3f %6.3f %8.3f %8.3f %4" FMT_Word " %4" FMT_Word "  (Gen: %2d)\n",
                    TimeToSecondsDbl(gc_cpu),
		    TimeToSecondsDbl(gc_elapsed),
		    TimeToSecondsDbl(cpu),
		    TimeToSecondsDbl(elapsed - start_init_elapsed),
		    faults - gct->gc_start_faults,
                        gct->gc_start_faults - GC_end_faults,
                    gen);

            GC_end_faults = faults;
	    statsFlush();
	}

        GC_coll_cpu[gen] += gc_cpu;
        GC_coll_elapsed[gen] += gc_elapsed;
        if (GC_coll_max_pause[gen] < gc_elapsed) {
            GC_coll_max_pause[gen] = gc_elapsed;
        }

	GC_tot_copied += (StgWord64) copied;
        GC_par_max_copied += (StgWord64) par_max_copied;
        GC_par_tot_copied += (StgWord64) par_tot_copied;
	GC_tot_cpu   += gc_cpu;
        
        traceEventHeapSize(cap,
	                   CAPSET_HEAP_DEFAULT,
			   mblocks_allocated * MBLOCK_SIZE_W * sizeof(W_));

	if (gen == RtsFlags.GcFlags.generations-1) { /* major GC? */
	    if (live > max_residency) {
		max_residency = live;
	    }
            current_residency = live;
	    residency_samples++;
	    cumulative_residency += live;
	    traceEventHeapLive(cap, 
    	    	    	       CAPSET_HEAP_DEFAULT,
	                       live * sizeof(W_));
	}

        if (slop > max_slop) max_slop = slop;
    }

    if (rub_bell) {
	debugBelch("\b\b\b  \b\b\b");
	rub_bell = 0;
    }

#if USE_PAPI
    if(papi_is_reporting) {
      /* Switch to counting mutator events */
      if (gen == 0) {
          papi_stop_gc0_count();
      } else {
          papi_stop_gc1_count();
      }
      papi_start_mutator_count();
    }
#endif
}

/* -----------------------------------------------------------------------------
   Called at the beginning of each Retainer Profiliing
   -------------------------------------------------------------------------- */
#ifdef PROFILING
void
stat_startRP(void)
{
    Time user, elapsed;
    getProcessTimes( &user, &elapsed );

    RP_start_time = user;
    RPe_start_time = elapsed;
}
#endif /* PROFILING */

/* -----------------------------------------------------------------------------
   Called at the end of each Retainer Profiliing
   -------------------------------------------------------------------------- */

#ifdef PROFILING
void
stat_endRP(
  nat retainerGeneration,
#ifdef DEBUG_RETAINER
  nat maxCStackSize,
  int maxStackSize,
#endif
  double averageNumVisit)
{
    Time user, elapsed;
    getProcessTimes( &user, &elapsed );

    RP_tot_time += user - RP_start_time;
    RPe_tot_time += elapsed - RPe_start_time;

  fprintf(prof_file, "Retainer Profiling: %d, at %f seconds\n", 
    retainerGeneration, mut_user_time_during_RP());
#ifdef DEBUG_RETAINER
  fprintf(prof_file, "\tMax C stack size = %u\n", maxCStackSize);
  fprintf(prof_file, "\tMax auxiliary stack size = %u\n", maxStackSize);
#endif
  fprintf(prof_file, "\tAverage number of visits per object = %f\n", averageNumVisit);
}
#endif /* PROFILING */

/* -----------------------------------------------------------------------------
   Called at the beginning of each heap census
   -------------------------------------------------------------------------- */
#ifdef PROFILING
void
stat_startHeapCensus(void)
{
    Time user, elapsed;
    getProcessTimes( &user, &elapsed );

    HC_start_time = user;
    HCe_start_time = elapsed;
}
#endif /* PROFILING */

/* -----------------------------------------------------------------------------
   Called at the end of each heap census
   -------------------------------------------------------------------------- */
#ifdef PROFILING
void
stat_endHeapCensus(void) 
{
    Time user, elapsed;
    getProcessTimes( &user, &elapsed );

    HC_tot_time += user - HC_start_time;
    HCe_tot_time += elapsed - HCe_start_time;
}
#endif /* PROFILING */

/* -----------------------------------------------------------------------------
   Called at the end of execution

   NOTE: number of allocations is not entirely accurate: it doesn't
   take into account the few bytes at the end of the heap that
   were left unused when the heap-check failed.
   -------------------------------------------------------------------------- */

#ifdef DEBUG
#define TICK_VAR_INI(arity) \
  StgInt SLOW_CALLS_##arity = 1; \
  StgInt RIGHT_ARITY_##arity = 1; \
  StgInt TAGGED_PTR_##arity = 0;

TICK_VAR_INI(1)
TICK_VAR_INI(2)

StgInt TOTAL_CALLS=1;
#endif

/* Report the value of a counter */
#define REPORT(counter) \
  { \
    showStgWord64(counter,temp,rtsTrue/*commas*/); \
    statsPrintf("  (" #counter ")  : %s\n",temp);				\
  }

/* Report the value of a counter as a percentage of another counter */
#define REPORT_PCT(counter,countertot) \
  statsPrintf("  (" #counter ") %% of (" #countertot ") : %.1f%%\n", \
	      counter*100.0/countertot)

#define TICK_PRINT(arity) \
  REPORT(SLOW_CALLS_##arity); \
  REPORT_PCT(RIGHT_ARITY_##arity,SLOW_CALLS_##arity); \
  REPORT_PCT(TAGGED_PTR_##arity,RIGHT_ARITY_##arity); \
  REPORT(RIGHT_ARITY_##arity); \
  REPORT(TAGGED_PTR_##arity)

#define TICK_PRINT_TOT(arity) \
  statsPrintf("  (SLOW_CALLS_" #arity ") %% of (TOTAL_CALLS) : %.1f%%\n", \
	      SLOW_CALLS_##arity * 100.0/TOTAL_CALLS)

static inline Time get_init_cpu(void) { return end_init_cpu - start_init_cpu; }
static inline Time get_init_elapsed(void) { return end_init_elapsed - start_init_elapsed; }


void
stat_exit (void)
{
    generation *gen;
    Time gc_cpu = 0;
    Time gc_elapsed = 0;
    Time init_cpu = 0;
    Time init_elapsed = 0;
    Time mut_cpu = 0;
    Time mut_elapsed = 0;
    Time exit_cpu = 0;
    Time exit_elapsed = 0;
    W_ tot_alloc;
    W_ alloc;

    if (RtsFlags.GcFlags.giveStats != NO_GC_STATS) {

	char temp[BIG_STRING_LEN];
	Time tot_cpu;
	Time tot_elapsed;
	nat i, g, total_collections = 0;

	getProcessTimes( &tot_cpu, &tot_elapsed );
	tot_elapsed -= start_init_elapsed;

        tot_alloc = calcTotalAllocated();

        // allocated since the last GC
        alloc = tot_alloc - GC_tot_alloc;
        GC_tot_alloc = tot_alloc;

	/* Count total garbage collections */
	for (g = 0; g < RtsFlags.GcFlags.generations; g++)
	    total_collections += generations[g].collections;

	/* avoid divide by zero if tot_cpu is measured as 0.00 seconds -- SDM */
	if (tot_cpu  == 0.0)  tot_cpu = 1;
	if (tot_elapsed == 0.0) tot_elapsed = 1;
	
	if (RtsFlags.GcFlags.giveStats >= VERBOSE_GC_STATS) {
	    statsPrintf("%9" FMT_SizeT " %9.9s %9.9s", (W_)alloc*sizeof(W_), "", "");
	    statsPrintf(" %6.3f %6.3f\n\n", 0.0, 0.0);
	}

        for (i = 0; i < RtsFlags.GcFlags.generations; i++) {
            gc_cpu     += GC_coll_cpu[i];
            gc_elapsed += GC_coll_elapsed[i];
        }

        // heapCensus() is called by the GC, so RP and HC time are
        // included in the GC stats.  We therefore subtract them to
        // obtain the actual GC cpu time.
        gc_cpu     -= PROF_VAL(RP_tot_time + HC_tot_time);
        gc_elapsed -= PROF_VAL(RPe_tot_time + HCe_tot_time);

        init_cpu     = get_init_cpu();
        init_elapsed = get_init_elapsed();

        exit_cpu     = end_exit_cpu - start_exit_cpu;
        exit_elapsed = end_exit_elapsed - start_exit_elapsed;

        mut_elapsed = start_exit_elapsed - end_init_elapsed - gc_elapsed;

        mut_cpu = start_exit_cpu - end_init_cpu - gc_cpu
            - PROF_VAL(RP_tot_time + HC_tot_time);
        if (mut_cpu < 0) { mut_cpu = 0; }

	if (RtsFlags.GcFlags.giveStats >= SUMMARY_GC_STATS) {
	    showStgWord64(GC_tot_alloc*sizeof(W_), 
				 temp, rtsTrue/*commas*/);
	    statsPrintf("%16s bytes allocated in the heap\n", temp);

	    showStgWord64(GC_tot_copied*sizeof(W_), 
				 temp, rtsTrue/*commas*/);
	    statsPrintf("%16s bytes copied during GC\n", temp);

            if ( residency_samples > 0 ) {
		showStgWord64(max_residency*sizeof(W_), 
				     temp, rtsTrue/*commas*/);
		statsPrintf("%16s bytes maximum residency (%" FMT_Word " sample(s))\n",
			temp, residency_samples);
	    }

	    showStgWord64(max_slop*sizeof(W_), temp, rtsTrue/*commas*/);
	    statsPrintf("%16s bytes maximum slop\n", temp);

	    statsPrintf("%16" FMT_SizeT " MB total memory in use (%" FMT_SizeT " MB lost due to fragmentation)\n\n", 
                        (size_t)(peak_mblocks_allocated * MBLOCK_SIZE_W) / (1024 * 1024 / sizeof(W_)),
                        (size_t)(peak_mblocks_allocated * BLOCKS_PER_MBLOCK * BLOCK_SIZE_W - hw_alloc_blocks * BLOCK_SIZE_W) / (1024 * 1024 / sizeof(W_)));

	    /* Print garbage collections in each gen */
            statsPrintf("                                     Tot time (elapsed)  Avg pause  Max pause\n");
            for (g = 0; g < RtsFlags.GcFlags.generations; g++) {
                gen = &generations[g];
                statsPrintf("  Gen %2d     %5d colls, %5d par   %6.3fs  %6.3fs     %3.4fs    %3.4fs\n",
                            gen->no,
                            gen->collections,
                            gen->par_collections,
                            TimeToSecondsDbl(GC_coll_cpu[g]),
                            TimeToSecondsDbl(GC_coll_elapsed[g]),
                            gen->collections == 0 ? 0 : TimeToSecondsDbl(GC_coll_elapsed[g] / gen->collections),
                            TimeToSecondsDbl(GC_coll_max_pause[g]));
            }

#if defined(THREADED_RTS)
            if (RtsFlags.ParFlags.parGcEnabled && n_capabilities > 1) {
                statsPrintf("\n  Parallel GC work balance: %.2f%% (serial 0%%, perfect 100%%)\n", 
                            100 * (((double)GC_par_tot_copied / (double)GC_par_max_copied) - 1)
                                / (n_capabilities - 1)
                    );
            }
#endif
            statsPrintf("\n");

#if defined(THREADED_RTS)
            statsPrintf("  TASKS: %d (%d bound, %d peak workers (%d total), using -N%d)\n",
                        taskCount, taskCount - workerCount,
                        peakWorkerCount, workerCount,
                        n_capabilities);

	    statsPrintf("\n");

            {
                nat i;
                SparkCounters sparks = { 0, 0, 0, 0, 0, 0};
                for (i = 0; i < n_capabilities; i++) {
                    sparks.created   += capabilities[i]->spark_stats.created;
                    sparks.dud       += capabilities[i]->spark_stats.dud;
                    sparks.overflowed+= capabilities[i]->spark_stats.overflowed;
                    sparks.converted += capabilities[i]->spark_stats.converted;
                    sparks.gcd       += capabilities[i]->spark_stats.gcd;
                    sparks.fizzled   += capabilities[i]->spark_stats.fizzled;
                }

                statsPrintf("  SPARKS: %" FMT_Word " (%" FMT_Word " converted, %" FMT_Word " overflowed, %" FMT_Word " dud, %" FMT_Word " GC'd, %" FMT_Word " fizzled)\n\n",
                            sparks.created + sparks.dud + sparks.overflowed,
                            sparks.converted, sparks.overflowed, sparks.dud,
                            sparks.gcd, sparks.fizzled);
            }
#endif

	    statsPrintf("  INIT    time  %7.3fs  (%7.3fs elapsed)\n",
                        TimeToSecondsDbl(init_cpu), TimeToSecondsDbl(init_elapsed));

            statsPrintf("  MUT     time  %7.3fs  (%7.3fs elapsed)\n",
                        TimeToSecondsDbl(mut_cpu), TimeToSecondsDbl(mut_elapsed));
            statsPrintf("  GC      time  %7.3fs  (%7.3fs elapsed)\n",
                        TimeToSecondsDbl(gc_cpu), TimeToSecondsDbl(gc_elapsed));

#ifdef PROFILING
	    statsPrintf("  RP      time  %7.3fs  (%7.3fs elapsed)\n",
		    TimeToSecondsDbl(RP_tot_time), TimeToSecondsDbl(RPe_tot_time));
	    statsPrintf("  PROF    time  %7.3fs  (%7.3fs elapsed)\n",
		    TimeToSecondsDbl(HC_tot_time), TimeToSecondsDbl(HCe_tot_time));
#endif 
	    statsPrintf("  EXIT    time  %7.3fs  (%7.3fs elapsed)\n",
		    TimeToSecondsDbl(exit_cpu), TimeToSecondsDbl(exit_elapsed));
	    statsPrintf("  Total   time  %7.3fs  (%7.3fs elapsed)\n\n",
		    TimeToSecondsDbl(tot_cpu), TimeToSecondsDbl(tot_elapsed));
#ifndef THREADED_RTS
	    statsPrintf("  %%GC     time     %5.1f%%  (%.1f%% elapsed)\n\n",
		    TimeToSecondsDbl(gc_cpu)*100/TimeToSecondsDbl(tot_cpu),
		    TimeToSecondsDbl(gc_elapsed)*100/TimeToSecondsDbl(tot_elapsed));
#endif

            if (mut_cpu == 0) {
		showStgWord64(0, temp, rtsTrue/*commas*/);
            } else {
		showStgWord64(
                    (StgWord64)((GC_tot_alloc*sizeof(W_)) / TimeToSecondsDbl(mut_cpu)),
                    temp, rtsTrue/*commas*/);
            }

	    statsPrintf("  Alloc rate    %s bytes per MUT second\n\n", temp);
	
	    statsPrintf("  Productivity %5.1f%% of total user, %.1f%% of total elapsed\n\n",
                    TimeToSecondsDbl(tot_cpu - gc_cpu -
				PROF_VAL(RP_tot_time + HC_tot_time) - init_cpu) * 100 
		    / TimeToSecondsDbl(tot_cpu), 
                    TimeToSecondsDbl(tot_cpu - gc_cpu -
                                PROF_VAL(RP_tot_time + HC_tot_time) - init_cpu) * 100
                    / TimeToSecondsDbl(tot_elapsed));

            /*
            TICK_PRINT(1);
            TICK_PRINT(2);
	    REPORT(TOTAL_CALLS);
            TICK_PRINT_TOT(1);
            TICK_PRINT_TOT(2);
            */

#if USE_PAPI
            papi_stats_report();
#endif
#if defined(THREADED_RTS) && defined(PROF_SPIN)
            {
                nat g;
                
                statsPrintf("gc_alloc_block_sync: %"FMT_Word64"\n", gc_alloc_block_sync.spin);
                statsPrintf("whitehole_spin: %"FMT_Word64"\n", whitehole_spin);
                for (g = 0; g < RtsFlags.GcFlags.generations; g++) {
                    statsPrintf("gen[%d].sync: %"FMT_Word64"\n", g, generations[g].sync.spin);
                }
            }
#endif
	}

	if (RtsFlags.GcFlags.giveStats == ONELINE_GC_STATS) {
      char *fmt1, *fmt2;
      if (RtsFlags.MiscFlags.machineReadable) {
          fmt1 = " [(\"bytes allocated\", \"%llu\")\n";
          fmt2 = " ,(\"num_GCs\", \"%d\")\n"
                 " ,(\"average_bytes_used\", \"%ld\")\n"
                 " ,(\"max_bytes_used\", \"%ld\")\n"
                 " ,(\"num_byte_usage_samples\", \"%ld\")\n"
                 " ,(\"peak_megabytes_allocated\", \"%lu\")\n"
                 " ,(\"init_cpu_seconds\", \"%.3f\")\n"
                 " ,(\"init_wall_seconds\", \"%.3f\")\n"
                 " ,(\"mutator_cpu_seconds\", \"%.3f\")\n"
                 " ,(\"mutator_wall_seconds\", \"%.3f\")\n"
                 " ,(\"GC_cpu_seconds\", \"%.3f\")\n"
                 " ,(\"GC_wall_seconds\", \"%.3f\")\n"
                 " ]\n";
      }
      else {
          fmt1 = "<<ghc: %llu bytes, ";
          fmt2 = "%d GCs, %ld/%ld avg/max bytes residency (%ld samples), %luM in use, %.3f INIT (%.3f elapsed), %.3f MUT (%.3f elapsed), %.3f GC (%.3f elapsed) :ghc>>\n";
      }
	  /* print the long long separately to avoid bugginess on mingwin (2001-07-02, mingw-0.5) */
	  statsPrintf(fmt1, GC_tot_alloc*(StgWord64)sizeof(W_));
	  statsPrintf(fmt2,
		    total_collections,
		    residency_samples == 0 ? 0 : 
		        cumulative_residency*sizeof(W_)/residency_samples, 
		    max_residency*sizeof(W_), 
		    residency_samples,
		    (unsigned long)(peak_mblocks_allocated * MBLOCK_SIZE / (1024L * 1024L)),
		    TimeToSecondsDbl(init_cpu), TimeToSecondsDbl(init_elapsed),
		    TimeToSecondsDbl(mut_cpu), TimeToSecondsDbl(mut_elapsed),
		    TimeToSecondsDbl(gc_cpu), TimeToSecondsDbl(gc_elapsed));
	}

	statsFlush();
	statsClose();
    }

    if (GC_coll_cpu) {
      stgFree(GC_coll_cpu);
      GC_coll_cpu = NULL;
    }
    if (GC_coll_elapsed) {
      stgFree(GC_coll_elapsed);
      GC_coll_elapsed = NULL;
    }
    if (GC_coll_max_pause) {
      stgFree(GC_coll_max_pause);
      GC_coll_max_pause = NULL;
    }

    /* Output STM stats */
    if (RtsFlags.ConcFlags.stmStats != 0)
    {
        stm_stats total;
        initSTMStatsValues(&total);

        lock_stm_stats();
        stm_stats_node* nodeStats = smp_stm_stats;
        smp_stm_stats = NULL;
        nat i;
        for (i = 0; i < n_capabilities; i++) {
          capabilities[i]->stm_stats = NULL;
        }
        unlock_stm_stats();

        stm_stats_node* node = nodeStats;

        debugBelch("STM stats:\n----------\nCap"
                    "   Starts        "
                    "  Aborts         "
                    "  Retry          "
                    "  Validate Fails "
                    "  Failed-wakeup  "
                    "  STM-commit     "
                    "  HTM-commit     "
                    "  STM-alloc-co-hp"
                    "  STM-alloc-co   "
                    "  STM-alloc-ab-hp"
                    "  STM-alloc-ab   "
                    "  No-record\n");

        while (node != NULL)
        {
            addSTMStats(&total, &node->stats);
            debugBelch("%3d ", node->cap_no);
            printSTMStats(&node->stats);
            debugBelch("\n");

            node = node->next;
        }

        debugBelch("    "); 
        printSTMStats(&total);
        debugBelch("\n");

        node = nodeStats;

        debugBelch("HTM stats:\n----------\nCap"
                    "   HTM-fallback  "
                    "  HTM-GC         "
                    "  HTM-fail       "
                    "  HLE-locked     "
                    "  HLE-fail       "
                    "  HLE-fallback   "
                    "  HLE-commit     "
                    "  HLE-release    "
                    "  Unaligned arr  "
                    "  access    arr  "
                    "  HTM-alloc-hp   "
                    "  HTM-alloc\n");

        while (node != NULL)
        {
            debugBelch("%3d ", node->cap_no);
            printHTMStats(&node->stats);
            debugBelch("\n");

            stm_stats_node* prev = node;
            node = node->next;
            stgFree(prev);
        }

        debugBelch("    "); 
        printHTMStats(&total);
        debugBelch("\n");

        printTMSizes();
        debugBelch("\n");

        printTMAllocStats(&total);
    }
}

/* -----------------------------------------------------------------------------
   stat_describe_gens

   Produce some detailed info on the state of the generational GC.
   -------------------------------------------------------------------------- */
void
statDescribeGens(void)
{
  nat g, mut, lge, i;
  W_ gen_slop;
  W_ tot_live, tot_slop;
  W_ gen_live, gen_blocks;
  bdescr *bd;
  generation *gen;
  
  debugBelch(
"----------------------------------------------------------\n"
"  Gen     Max  Mut-list  Blocks    Large     Live     Slop\n"
"       Blocks     Bytes          Objects                  \n"
"----------------------------------------------------------\n");

  tot_live = 0;
  tot_slop = 0;

  for (g = 0; g < RtsFlags.GcFlags.generations; g++) {
      gen = &generations[g];

      for (bd = gen->large_objects, lge = 0; bd; bd = bd->link) {
          lge++;
      }

      gen_live   = genLiveWords(gen);
      gen_blocks = genLiveBlocks(gen);

      mut = 0;
      for (i = 0; i < n_capabilities; i++) {
          mut += countOccupied(capabilities[i]->mut_lists[g]);

          // Add the pinned object block.
          bd = capabilities[i]->pinned_object_block;
          if (bd != NULL) {
              gen_live   += bd->free - bd->start;
              gen_blocks += bd->blocks;
          }

          gen_live   += gcThreadLiveWords(i,g);
          gen_blocks += gcThreadLiveBlocks(i,g);
      }

      debugBelch("%5d %7" FMT_Word " %9d", g, (W_)gen->max_blocks, mut);

      gen_slop = gen_blocks * BLOCK_SIZE_W - gen_live;

      debugBelch("%8" FMT_Word " %8d %8" FMT_Word " %8" FMT_Word "\n", gen_blocks, lge,
                 gen_live*(W_)sizeof(W_), gen_slop*(W_)sizeof(W_));
      tot_live += gen_live;
      tot_slop += gen_slop;
  }
  debugBelch("----------------------------------------------------------\n");
  debugBelch("%41s%8" FMT_SizeT " %8" FMT_SizeT "\n",
             "",tot_live*sizeof(W_),tot_slop*sizeof(W_));
  debugBelch("----------------------------------------------------------\n");
  debugBelch("\n");
}

/* -----------------------------------------------------------------------------
   Stats available via a programmatic interface, so eg. GHCi can time
   each compilation and expression evaluation.
   -------------------------------------------------------------------------- */

extern HsInt64 getAllocations( void ) 
{ return (HsInt64)GC_tot_alloc * sizeof(W_); }

/* EZY: I'm not convinced I got all the casting right. */

extern rtsBool getGCStatsEnabled( void )
{
    return RtsFlags.GcFlags.giveStats != NO_GC_STATS;
}

extern void getGCStats( GCStats *s )
{
    nat total_collections = 0;
    nat g;
    Time gc_cpu = 0;
    Time gc_elapsed = 0;
    Time current_elapsed = 0;
    Time current_cpu = 0;

    getProcessTimes(&current_cpu, &current_elapsed);

    /* EZY: static inline'ify these */
    for (g = 0; g < RtsFlags.GcFlags.generations; g++)
        total_collections += generations[g].collections;

    for (g = 0; g < RtsFlags.GcFlags.generations; g++) {
        gc_cpu     += GC_coll_cpu[g];
        gc_elapsed += GC_coll_elapsed[g];
    }

    s->bytes_allocated = GC_tot_alloc*(StgWord64)sizeof(W_);
    s->num_gcs = total_collections;
    s->num_byte_usage_samples = residency_samples;
    s->max_bytes_used = max_residency*sizeof(W_);
    s->cumulative_bytes_used = cumulative_residency*(StgWord64)sizeof(W_);
    s->peak_megabytes_allocated = (StgWord64)(peak_mblocks_allocated * MBLOCK_SIZE / (1024L * 1024L));
    s->bytes_copied = GC_tot_copied*(StgWord64)sizeof(W_);
    s->max_bytes_slop = max_slop*(StgWord64)sizeof(W_);
    s->current_bytes_used = current_residency*(StgWord64)sizeof(W_);
    s->current_bytes_slop = current_slop*(StgWord64)sizeof(W_);
    /*
    s->init_cpu_seconds = TimeToSecondsDbl(get_init_cpu());
    s->init_wall_seconds = TimeToSecondsDbl(get_init_elapsed());
    */
    s->mutator_cpu_seconds = TimeToSecondsDbl(current_cpu - end_init_cpu - gc_cpu - PROF_VAL(RP_tot_time + HC_tot_time));
    s->mutator_wall_seconds = TimeToSecondsDbl(current_elapsed- end_init_elapsed - gc_elapsed);
    s->gc_cpu_seconds = TimeToSecondsDbl(gc_cpu);
    s->gc_wall_seconds = TimeToSecondsDbl(gc_elapsed);
    /* EZY: Being consistent with incremental output, but maybe should also discount init */
    s->cpu_seconds = TimeToSecondsDbl(current_cpu);
    s->wall_seconds = TimeToSecondsDbl(current_elapsed - end_init_elapsed);
    s->par_tot_bytes_copied = GC_par_tot_copied*(StgWord64)sizeof(W_);
    s->par_max_bytes_copied = GC_par_max_copied*(StgWord64)sizeof(W_);
}
// extern void getTaskStats( TaskStats **s ) {}
#if 0
extern void getSparkStats( SparkCounters *s ) {
    nat i;
    s->created = 0;
    s->dud = 0;
    s->overflowed = 0;
    s->converted = 0;
    s->gcd = 0;
    s->fizzled = 0;
    for (i = 0; i < n_capabilities; i++) {
        s->created   += capabilities[i]->spark_stats.created;
        s->dud       += capabilities[i]->spark_stats.dud;
        s->overflowed+= capabilities[i]->spark_stats.overflowed;
        s->converted += capabilities[i]->spark_stats.converted;
        s->gcd       += capabilities[i]->spark_stats.gcd;
        s->fizzled   += capabilities[i]->spark_stats.fizzled;
    }
}
#endif

/* -----------------------------------------------------------------------------
   Dumping stuff in the stats file, or via the debug message interface
   -------------------------------------------------------------------------- */

void
statsPrintf( char *s, ... )
{
    FILE *sf = RtsFlags.GcFlags.statsFile;
    va_list ap;
    
    va_start(ap,s);
    if (sf == NULL) {
	vdebugBelch(s,ap);
    } else {
	vfprintf(sf, s, ap);
    }
    va_end(ap);
}

static void
statsFlush( void )
{
    FILE *sf = RtsFlags.GcFlags.statsFile;
    if (sf != NULL) {
	fflush(sf);
    }
}

static void
statsClose( void )
{
    FILE *sf = RtsFlags.GcFlags.statsFile;
    if (sf != NULL) {
	fclose(sf);
    }
}

// Local Variables:
// mode: C
// fill-column: 80
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
