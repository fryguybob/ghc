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
void      stat_endGC  (Capability *cap, struct gc_thread_ *_gct, W_ live,
                       W_ copied, W_ slop, uint32_t gen, uint32_t n_gc_threads,
                       W_ par_max_copied, W_ par_tot_copied);

/* STM Stats*/
typedef struct stm_stats_
{
    W_ start;         /* Transactions started */
    W_ abort;         /* Transactions aborted due to conflict */
    W_ retry;         /* Successfully blocked transactions */
    W_ validate_fail; /* Failure to validate an STM transaction */
    W_ failed_wakeup; /* wakeups that lead to subsequent retry */

    W_ stm_commit;    /* Commit of an STM transaction */
    W_ htm_commit;    /* Commit of an HTM transaction */
    W_ htm_fallback;  /* Transaction that gave up and switched to STM */
    W_ htm_fail;      /* HTM hardware abort */
    W_ htm_gc;        /* Need for GC killed HTM */

    W_ hle_locked;    /* STM lock was observed as locked by HLE */
    W_ hle_fail;      /* HLE aborted */
    W_ hle_fallback;  /* HLE gave up */
    W_ hle_commit;    /* HLE success */
    W_ hle_release;   /* Full STM fallback released lock */
} stm_stats;

typedef struct stm_stats_node_
{
    struct stm_stats_node_  *next;
    W_                       cap_no;
    stm_stats                stats;
} stm_stats_node;

void initSTMStats(Capability* cap);


#ifdef PROFILING
void      stat_startRP(void);
void      stat_endRP(uint32_t,
#ifdef DEBUG_RETAINER
                            uint32_t, int,
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

void      statDescribeGens( void );

Time      stat_getElapsedGCTime(void);
Time      stat_getElapsedTime(void);

#include "EndPrivate.h"

#endif /* STATS_H */
