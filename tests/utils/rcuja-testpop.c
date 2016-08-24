/*
 * rcuja/testpop.c
 *
 * Userspace RCU library - RCU Judy Array population size test
 *
 * Copyright 2012-2013 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

/*
 * This program generates random populations, and shows the largest
 * sub-class generated, as well as the distribution of sub-class size
 * for the largest sub-class of each population.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>
#include <limits.h>
#include <assert.h>

static int sel_pool_len = 50;	/* default */
static int nr_distrib = 2;	/* default */
//#define SEL_POOL_LEN	100
//#define NR_POOLS	10000000ULL

static uint8_t pool[256];
static uint8_t nr_one[8];
static uint8_t nr_2d_11[8][8];
static uint8_t nr_2d_10[8][8];
static uint8_t nr_2d_01[8][8];
static uint8_t nr_2d_00[8][8];
static int global_max_minsubclass_len = 0;

static unsigned int subclass_len_distrib[256];

static int verbose;

static
uint8_t random_char(void)
{
	return (uint8_t) random();
}

static
void print_pool(void)
{
	int i;

	printf("pool: ");
	for (i = 0; i < sel_pool_len; i++) {
		printf("%d ", (int) pool[i]);
	}
	printf("\n");
}

static
void gen_pool(void)
{
	uint8_t src_pool[256];
	int i;
	int nr_left = 256;

	memset(pool, 0, sizeof(pool));
	for (i = 0; i < 256; i++)
		src_pool[i] = (uint8_t) i;
	for (i = 0; i < sel_pool_len; i++) {
		int sel;

		sel = random_char() % nr_left;
		pool[i] = src_pool[sel];
		src_pool[sel] = src_pool[nr_left - 1];
		nr_left--;
	}
}

static
void count_pool(void)
{
	int i;

	memset(nr_one, 0, sizeof(nr_one));
	memset(nr_2d_11, 0, sizeof(nr_2d_11));
	memset(nr_2d_10, 0, sizeof(nr_2d_10));
	memset(nr_2d_01, 0, sizeof(nr_2d_01));
	memset(nr_2d_00, 0, sizeof(nr_2d_00));

	for (i = 0; i < sel_pool_len; i++) {
		if (nr_distrib == 2) {
			int j;

			for (j = 0; j < 8; j++) {
				if (pool[i] & (1U << j))
					nr_one[j]++;
			}
		}

		if (nr_distrib == 4) {
			int bit_i, bit_j;

			for (bit_i = 0; bit_i < 8; bit_i++) {
				for (bit_j = 0; bit_j < bit_i; bit_j++) {
					if (pool[i] & (1U << bit_i)) {
						if (pool[i] & (1U << bit_j)) {
							nr_2d_11[bit_i][bit_j]++;
						} else {
							nr_2d_10[bit_i][bit_j]++;
						}
					} else {
						if (pool[i] & (1U << bit_j)) {
							nr_2d_01[bit_i][bit_j]++;
						} else {
							nr_2d_00[bit_i][bit_j]++;
						}
					}
				}
			}
		}
	}
}

static
void print_count(void)
{
	int i;

	printf("pool distribution:\n");

	if (nr_distrib == 2) {
		printf("  0      1\n");
		printf("----------\n");
		for (i = 0; i < 8; i++) {
			printf("%3d    %3d\n",
				sel_pool_len - nr_one[i], nr_one[i]);
		}
	}

	if (nr_distrib == 4) {
		/* TODO */
	}
	printf("\n");
}

static
void stat_count_1d(void)
{
	unsigned int overall_best_distance = UINT_MAX;
	unsigned int overall_minsubclass_len;
	int i;

	for (i = 0; i < 8; i++) {
		int distance_to_best;

		distance_to_best = ((unsigned int) nr_one[i] << 1U) - sel_pool_len;
		if (distance_to_best < 0)
			distance_to_best = -distance_to_best;
		if (distance_to_best < overall_best_distance) {
			overall_best_distance = distance_to_best;
		}
	}
	overall_minsubclass_len = (overall_best_distance + sel_pool_len) >> 1UL;
	if (overall_minsubclass_len > global_max_minsubclass_len) {
		global_max_minsubclass_len = overall_minsubclass_len;
	}
	subclass_len_distrib[overall_minsubclass_len]++;
}

static
void stat_count_2d(void)
{
	int overall_best_distance = INT_MAX;
	unsigned int overall_minsubclass_len = 0;
	int bit_i, bit_j;

	for (bit_i = 0; bit_i < 8; bit_i++) {
		for (bit_j = 0; bit_j < bit_i; bit_j++) {
			int distance_to_best[4], subclass_len[4];

			distance_to_best[0] = ((unsigned int) nr_2d_11[bit_i][bit_j] << 2U) - sel_pool_len;
			distance_to_best[1] = ((unsigned int) nr_2d_10[bit_i][bit_j] << 2U) - sel_pool_len;
			distance_to_best[2] = ((unsigned int) nr_2d_01[bit_i][bit_j] << 2U) - sel_pool_len;
			distance_to_best[3] = ((unsigned int) nr_2d_00[bit_i][bit_j] << 2U) - sel_pool_len;

			subclass_len[0] = nr_2d_11[bit_i][bit_j];
			subclass_len[1] = nr_2d_10[bit_i][bit_j];
			subclass_len[2] = nr_2d_01[bit_i][bit_j];
			subclass_len[3] = nr_2d_00[bit_i][bit_j];

			/* Consider worse distance above best */
			if (distance_to_best[1] > 0 && distance_to_best[1] > distance_to_best[0]) {
				distance_to_best[0] = distance_to_best[1];
				subclass_len[0] = subclass_len[1];
			}
			if (distance_to_best[2] > 0 && distance_to_best[2] > distance_to_best[0]) {
				distance_to_best[0] = distance_to_best[2];
				subclass_len[0] = subclass_len[2];
			}
			if (distance_to_best[3] > 0 && distance_to_best[3] > distance_to_best[0]) {
				distance_to_best[0] = distance_to_best[3];
				subclass_len[0] = subclass_len[3];
			}

			/*
			 * If our worse distance is better than overall,
			 * we become new best candidate.
			 */
			if (distance_to_best[0] < overall_best_distance) {
				overall_best_distance = distance_to_best[0];
				overall_minsubclass_len = subclass_len[0];
			}
		}
	}
	if (overall_minsubclass_len > global_max_minsubclass_len) {
		global_max_minsubclass_len = overall_minsubclass_len;
	}
	subclass_len_distrib[overall_minsubclass_len]++;
}

static
void stat_count(void)
{
	switch (nr_distrib) {
	case 2:
		stat_count_1d();
		break;
	case 4:
		stat_count_2d();
		break;
	default:
		assert(0);
		break;
	}
}

static
void print_distrib(void)
{
	int i;
	unsigned long long tot = 0;

	for (i = 0; i < 256; i++) {
		tot += subclass_len_distrib[i];
	}
	if (tot == 0)
		return;
	printf("Distribution:\n");
	for (i = 0; i < 256; i++) {
		if (!subclass_len_distrib[i])
			continue;
		printf("(%u, %u, %llu%%) ",
			i, subclass_len_distrib[i],
			100 * (unsigned long long) subclass_len_distrib[i] / tot);
	}
	printf("\n");
}

static
void print_stat(uint64_t i)
{
	printf("after %llu pools, global_max_minsubclass_len: %d\n",
		(unsigned long long) i, global_max_minsubclass_len);
	print_distrib();
}

int main(int argc, char **argv)
{
	uint64_t i = 0;

	srandom(time(NULL));

	if (argc > 1) {
		sel_pool_len = atoi(argv[1]);
		if (sel_pool_len > 256 || sel_pool_len < 1) {
			printf("Wrong pool len\n");
			return -1;
		}
	}
	printf("pool len: %d\n", sel_pool_len);

	if (argc > 2) {
		nr_distrib = atoi(argv[2]);
		if (nr_distrib > 256 || nr_distrib < 1) {
			printf("Wrong number of distributions\n");
			return -1;
		}
	}

	if (argc > 3) {
		if (!strcmp(argv[3], "-v")) {
			verbose = 1;
		}
	}

	printf("pool distributions: %d\n", nr_distrib);

	if (nr_distrib != 2 && nr_distrib != 4) {
		printf("Wrong number of distributions. Only 2 and 4 supported.\n");
		return -1;
	}

	//for (i = 0; i < NR_POOLS; i++) {
	while (1) {
		gen_pool();
		count_pool();
		if (verbose) {
			print_pool();
			print_count();
		}
		stat_count();
		if (!(i % 100000ULL))
			print_stat(i);
		i++;
	}
	print_stat(i);
	print_distrib();

	return 0;
}
