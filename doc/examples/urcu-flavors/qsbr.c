// SPDX-FileCopyrightText: 2013 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
//
// SPDX-License-Identifier: LGPL-2.1-or-later

#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include <urcu/urcu-qsbr.h>	/* QSBR RCU flavor */
#include <urcu/rculist.h>	/* List example */
#include <urcu/compiler.h>	/* For CAA_ARRAY_SIZE */

/*
 * Example showing how to use the QSBR Userspace RCU flavor.
 *
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

	node = calloc(1, sizeof(*node));
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

int main(void)
{
	uint64_t values[] = { 42, 36, 24, };
	unsigned int i;
	int ret;
	struct mynode *node, *n;

	/*
	 * Each thread need using RCU read-side need to be explicitly
	 * registered.
	 */
	urcu_qsbr_register_thread();

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
	 * RCU traversal of the linked list.
	 */
	cds_list_for_each_entry_rcu(node, &mylist, node) {
		printf("Value: %" PRIu64 "\n", node->value);
	}

	/*
	 * Removing nodes from linked list. Safe against concurrent RCU
	 * traversals, require mutual exclusion with list updates.
	 */
	cds_list_for_each_entry_safe(node, n, &mylist, node) {
		cds_list_del_rcu(&node->node);
		/*
		 * call_rcu() will ensure that the handler
		 * "rcu_free_node" is executed after a grace period.
		 * call_rcu() can be called from RCU read-side critical
		 * sections.
		 */
		urcu_qsbr_call_rcu(&node->rcu_head, rcu_free_node);
	}

	/*
	 * For QSBR flavor, we need to explicitly announce quiescent
	 * states. Here is how it is done. This should be performed by
	 * every online registered RCU threads in the program
	 * periodically.
	 */
	urcu_qsbr_quiescent_state();

	/*
	 * For QSBR flavor, when a thread needs to be in a quiescent
	 * state for a long period of time, we use rcu_thread_offline()
	 * and rcu_thread_online().
	 */
	urcu_qsbr_thread_offline();

	sleep(1);

	urcu_qsbr_thread_online();

	/*
	 * We can also wait for a quiescent state by calling
	 * synchronize_rcu() rather than using call_rcu(). It is usually
	 * a slower approach than call_rcu(), because the latter can
	 * batch work. Moreover, call_rcu() can be called from a RCU
	 * read-side critical section, but synchronize_rcu() ensures the
	 * caller thread is offline, thus acting as a quiescent state.
	 */
	urcu_qsbr_synchronize_rcu();

	/*
	 * Waiting for previously called call_rcu handlers to complete
	 * before program exits, or in library destructors, is a good
	 * practice.
	 */
	urcu_qsbr_barrier();

end:
	urcu_qsbr_unregister_thread();
	return ret;
}
