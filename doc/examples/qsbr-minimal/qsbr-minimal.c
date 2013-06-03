/*
 * Copyright (C) 2013  Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

#define _LGPL_SOURCE
#include <urcu-qsbr.h>
#include <urcu/rculist.h>
#include <urcu/compiler.h>

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

/*
 * This is a mock-up example where updates and RCU traversals are
 * performed by the same thread to keep things simple on purpose.
 */

static CDS_LIST_HEAD(mylist);

struct mynode {
	uint64_t value;
	struct cds_list_head node;	/* linked-list chaining */
	struct rcu_head rcu_head;	/* for call_rcu() */
};

static
int add_node(uint64_t v)
{
	struct mynode *node;

	node = calloc(sizeof(*node), 1);
	if (!node)
		return -1;
	node->value = v;
	cds_list_add_rcu(&node->node, &mylist);
	return 0;
}

static
void rcu_free_node(struct rcu_head *rh)
{
	struct mynode *node = caa_container_of(rh, struct mynode, rcu_head);

	free(node);
}

int main(int argc, char **argv)
{
	uint64_t values[] = { 42, 36, 24, };
	unsigned int i;
	int ret;
	struct mynode *node, *n;

	/*
	 * Each thread need using RCU read-side need to be explicitely
	 * registered.
	 */
	rcu_register_thread();

	/*
	 * Adding nodes to the linked-list. Safe against concurrent
	 * RCU traversals, require mutual exclusion with list updates.
	 */
	for (i = 0; i < CAA_ARRAY_SIZE(values); i++) {
		ret = add_node(values[i]);
		if (ret)
			goto end;
	}

	/*
	 * For all RCU flavors except QSBR, we need to explicitly mark
	 * RCU read-side critical sections with rcu_read_lock() and
	 * rcu_read_unlock(). They can be nested. Those are no-ops for
	 * the QSBR flavor.
	 */
	rcu_read_lock();

	/*
	 * RCU traversal of the linked list.
	 */
	cds_list_for_each_entry_rcu(node, &mylist, node) {
		printf("Value: %" PRIu64 "\n", node->value);
	}
	rcu_read_unlock();

	/*
	 * Removing nodes from linked list. Safe against concurrent RCU
	 * traversals, require mutual exclusion with list updates.
	 */
	cds_list_for_each_entry_safe(node, n, &mylist, node) {
		cds_list_del_rcu(&node->node);
		call_rcu(&node->rcu_head, rcu_free_node);
	}

	/*
	 * For QSBR flavor, we need to explicitly announce quiescent
	 * states.
	 */
	rcu_quiescent_state();

	/*
	 * For QSBR flavor, when a thread needs to be in a quiescent
	 * state for a long period of time, we use rcu_thread_offline()
	 * and rcu_thread_online().
	 */
	rcu_thread_offline();

	sleep(1);

	rcu_thread_online();

	/*
	 * Waiting for previously called call_rcu handlers to complete
	 * before program exits is a good practice.
	 */
	rcu_barrier();

end:
	rcu_unregister_thread();
	return ret;
}
