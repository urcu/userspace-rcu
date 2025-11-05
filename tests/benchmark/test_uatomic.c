/*
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * SPDX-FileCopyrightText: 2025 Olivier Dion <odion@efficios.com>.
 *
 * test_uatomic.c - Trivial micro-benchmark of the uatomic API.
 *
 * The benchmark will print a summary like so:
 *
 *   memory-order: CMM_RELAXED
 *   uatomic_load_mo: 0.119530
 *   uatomic_store_mo: 0.129159
 *   uatomic_xchg_mo: 1.832290
 *   uatomic_cmpxchg_mo: 1.796460
 *   memory-order: CMM_SEQ_CST
 *   uatomic_load_mo: 0.206869
 *   uatomic_store_mo: 1.591636
 *   uatomic_xchg_mo: 1.600575
 *   uatomic_cmpxchg_mo: 1.800107
 *   memory-order: CMM_SEQ_CST_FENCE
 *   uatomic_load_mo: 1.512201
 *   uatomic_store_mo: 1.590643
 *   uatomic_xchg_mo: 1.596536
 *   uatomic_cmpxchg_mo: 1.801630
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

#define RUN_TEST(OP, ...)						\
	({								\
		uint64_t then, now;					\
		long value;						\
		then = gettime();					\
		for (size_t k = 0; k < LOOP_COUNT; ++k) {		\
			OP(&value, ##__VA_ARGS__);			\
		}							\
		now = gettime();					\
		printf("%s: %.6f\n", #OP, (now - then) / (double)LOOP_COUNT); \
	})

#define RUN_TESTS(MO)						\
	do {							\
		printf("memory-order: " #MO "\n");		\
		RUN_TEST(uatomic_load_mo, MO);			\
		RUN_TEST(uatomic_store_mo, 0, MO);		\
		RUN_TEST(uatomic_xchg_mo, 0, MO);		\
		RUN_TEST(uatomic_cmpxchg_mo, 0, 0, MO, MO);	\
	} while (0)

int main(void)
{
	RUN_TESTS(CMM_RELAXED);
	RUN_TESTS(CMM_SEQ_CST);
	RUN_TESTS(CMM_SEQ_CST_FENCE);

	return 0;
}
