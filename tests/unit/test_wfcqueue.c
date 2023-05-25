/*
 * test_wfcqueue.c
 *
 * Userspace RCU library - test wfcqueue race conditions
 *
 * Copyright 2023 - Olivier Dion <odion@efficios.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

#define _LGPL_SOURCE

#include <stdlib.h>

#include <pthread.h>

#include <urcu/wfcqueue.h>

#include "tap.h"

#define NR_TESTS 1
#define NR_PRODUCERS 4
#define LOOP 100

struct queue {
	struct cds_wfcq_head head;
	struct cds_wfcq_tail tail;
};

static void async_run(struct queue *queue)
{
	struct cds_wfcq_node *node = malloc(sizeof(*node));

	cds_wfcq_node_init(node);

	cds_wfcq_enqueue(&queue->head, &queue->tail, node);
}
static void do_async_loop(size_t *k, struct queue *queue)
{
	struct queue my_queue;
	enum cds_wfcq_ret state;
	struct cds_wfcq_node *node, *next;

	cds_wfcq_init(&my_queue.head, &my_queue.tail);

	state = cds_wfcq_splice_blocking(&my_queue.head,
					&my_queue.tail,
					&queue->head,
					&queue->tail);

	if (state == CDS_WFCQ_RET_SRC_EMPTY) {
		return;
	}

	__cds_wfcq_for_each_blocking_safe(&my_queue.head,
					&my_queue.tail,
					node, next) {
		free(node);
		(*k)++;
	}
}

static void *async_loop(void *queue)
{
	size_t k = 0;

	while (k < LOOP * NR_PRODUCERS) {
		(void) poll(NULL, 0, 10);
		do_async_loop(&k, queue);
	}

	return NULL;
}

static void *spawn_jobs(void *queue)
{
	for (size_t k = 0; k < LOOP; ++k) {
		async_run(queue);
	}

	return 0;
}

int main(void)
{
	pthread_t consumer;
	pthread_t producers[NR_PRODUCERS];
	struct queue queue;

	plan_tests(NR_TESTS);

	cds_wfcq_init(&queue.head, &queue.tail);
	pthread_create(&consumer, NULL, async_loop, &queue);

	for (size_t k = 0; k < NR_PRODUCERS; ++k) {
		pthread_create(&producers[k], NULL, spawn_jobs, &queue);
	}

	pthread_join(consumer, NULL);
	for (size_t k = 0; k < NR_PRODUCERS; ++k) {
		pthread_join(producers[k], NULL);
	}

	ok1("No race conditions");

	return exit_status();
}
