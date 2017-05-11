/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2005
 *
 * Statistics and timing-related functions.
 *
 * ---------------------------------------------------------------------------*/

#ifndef STATS_H
#define STATS_H

#include "GetTime.h"

#include "BeginPrivate.h"

#if defined(mingw32_HOST_OS)
/* On Win64, if we say "printf" then gcc thinks we are going to use
   MS format specifiers like %I64d rather than %llu */
#define PRINTF gnu_printf
#else
/* However, on OS X, "gnu_printf" isn't recognised */
#define PRINTF printf
#endif

struct gc_thread_;

void      stat_startInit(void);
void      stat_endInit(void);

void      stat_startGCSync(struct gc_thread_ *_gct);
void      stat_startGC(Capability *cap, struct gc_thread_ *_gct);
void      stat_endGC  (Capability *cap, struct gc_thread_ *_gct,
                       W_ live, W_ copied, W_ slop, nat gen,
                       nat n_gc_threads, W_ par_max_copied, W_ par_tot_copied);

void      stat_stm_accum(nat* w, nat v);

/* STM Stats*/
typedef struct stm_stats_
{
    nat start;         /* Transactions started */
    nat abort;         /* Transactions aborted due to conflict */
    nat retry;         /* Successfully blocked transactions */
    nat validate_fail; /* Failure to validate an STM transaction */
    nat failed_wakeup; /* wakeups that lead to subsequent retry */

    nat stm_commit;    /* Commit of an STM transaction */
    nat htm_commit;    /* Commit of an HTM transaction */
    nat htm_fallback;  /* Transaction that gave up and switched to STM */
    nat htm_fail;      /* HTM hardware abort */
    nat htm_gc;        /* Need for GC killed HTM */

    nat hle_locked;    /* STM lock was observed as locked by HLE */
    nat hle_fail;      /* HLE aborted */
    nat hle_fallback;  /* HLE gave up */
    nat hle_commit;    /* HLE success */
    nat hle_release;   /* Full STM fallback released lock */

    nat htm_alloc_hp;        /* Count bytes allocated while running committed HTM transactions */
    nat htm_alloc;           /* Count bytes allocated using allocate in committed HTM transactions */
    nat stm_alloc_committed_hp; /* Count bytes allocated while running committed STM transactions */
    nat stm_alloc_committed; /* Count bytes allocated using allocate in committed STM transactions */
    nat stm_alloc_aborted_hp;/* Count bytes allocated while running aborted STM transactions */
    nat stm_alloc_aborted;   /* Count bytes allocated using allocate in aborted STM transactions */
    nat alloc_snapshot;      /* Temporary holder for current transaction's allocation */
    nat no_record;           /* Count times we could not record allocation info */
} stm_stats;

typedef struct stm_stats_node_
{
    struct stm_stats_node_  *next;
    nat                      cap_no;
    stm_stats                stats;
} stm_stats_node;

void initSTMStats(Capability* cap);


#ifdef PROFILING
void      stat_startRP(void);
void      stat_endRP(nat, 
#ifdef DEBUG_RETAINER
                            nat, int, 
#endif
                            double);
#endif /* PROFILING */

#if defined(PROFILING) || defined(DEBUG)
void      stat_startHeapCensus(void);
void      stat_endHeapCensus(void);
#endif

void      stat_startExit(void);
void      stat_endExit(void);

void      stat_exit(void);
void      stat_workerStop(void);

void      initStats0(void);
void      initStats1(void);

double    mut_user_time_until(Time t);
double    mut_user_time(void);

#ifdef PROFILING
double    mut_user_time_during_RP(void);
double    mut_user_time_during_heap_census(void);
#endif /* PROFILING */

void      statDescribeGens( void );

Time      stat_getElapsedGCTime(void);
Time      stat_getElapsedTime(void);

#include "EndPrivate.h"

#endif /* STATS_H */
