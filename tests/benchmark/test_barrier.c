/*
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * SPDX-FileCopyrightText: 2025 Olivier Dion <odion@efficios.com>.
 * SPDX-FileCopyrightText: 2025 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * test_uatomic.c - Trivial micro-benchmark of the "cmm_" API memory barriers.
 *
 * The benchmark will print a summary like so:
 *
 * cmm_mb: 14.558424
 * cmm_smp_mb: 1.691178
 * cmm_rmb: 3.026440
 * cmm_smp_rmb: 0.256247
 * cmm_wmb: 0.244781
 * cmm_smp_wmb: 0.249728
 *
 * The values are nanoseconds per operation.
 */

#include <stdio.h>
#include <time.h>

#include <urcu/uatomic.h>

#define NSEC_PER_SEC	1000000000UL

/*
 * Average of 1 billion operations.
 */
#define LOOP_COUNT	1000000000UL

static uint64_t gettime(void)
{
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return (uint64_t)ts.tv_sec * NSEC_PER_SEC + ts.tv_nsec;
}

#define RUN_TEST(OP)							\
	({								\
		uint64_t then, now;					\
		then = gettime();					\
		for (size_t k = 0; k < LOOP_COUNT; ++k) {		\
			OP();						\
		}							\
		now = gettime();					\
		printf("%s: %.6f\n", #OP, (now - then) / (double)LOOP_COUNT); \
	})

#define RUN_TESTS()						\
	do {							\
		RUN_TEST(cmm_mb);				\
		RUN_TEST(cmm_smp_mb);				\
		RUN_TEST(cmm_rmb);				\
		RUN_TEST(cmm_smp_rmb);				\
		RUN_TEST(cmm_wmb);				\
		RUN_TEST(cmm_smp_wmb);				\
	} while (0)

int main(void)
{
	RUN_TESTS();

	return 0;
}
