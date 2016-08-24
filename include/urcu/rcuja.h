#ifndef _URCU_RCUJA_H
#define _URCU_RCUJA_H

/*
 * urcu/rcuja.h
 *
 * Userspace RCU library - RCU Judy Array
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
 *
 * Include this file _after_ including your URCU flavor.
 */

#include <urcu/compiler.h>
#include <urcu-call-rcu.h>
#include <urcu-flavor.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Duplicate nodes with the same key are chained into a singly-linked
 * list. The last item of this list has a NULL next pointer.
 */
struct cds_ja_node {
	struct cds_ja_node *next;
};

struct cds_ja;

/*
 * cds_ja_node_init - initialize a judy array node
 * @node: the node to initialize.
 *
 * This function is kept to be eventually used for debugging purposes
 * (detection of memory corruption).
 */
static inline
void cds_ja_node_init(struct cds_ja_node *node)
{
}

/*
 * Note: key UINT64_MAX is reserved internally for iteration.
 */

/*
 * cds_ja_lookup - look up by key.
 * @ja: the Judy array.
 * @key: key to look up.
 *
 * Returns the first node of a duplicate chain if a match is found, else
 * returns NULL.
 * A RCU read-side lock should be held across call to this function and
 * use of its return value.
 */
struct cds_ja_node *cds_ja_lookup(struct cds_ja *ja, uint64_t key);

/*
 * cds_ja_lookup_below_equal - look up first node with key <= @key.
 * @ja: the Judy array.
 * @key: key to look up.
 * @result_key: key found.
 *
 * Returns the first node of a duplicate chain if a node is present in
 * the tree which has a key below or equal to @key, else returns NULL.
 * A RCU read-side lock should be held across call to this function and
 * use of its return value.
 */
struct cds_ja_node *cds_ja_lookup_below_equal(struct cds_ja *ja,
		uint64_t key, uint64_t *result_key);

/*
 * cds_ja_lookup_above_equal - look up first node with key >= @key.
 * @ja: the Judy array.
 * @key: key to look up.
 * @result_key: key found.
 *
 * Returns the first node of a duplicate chain if a node is present in
 * the tree which has a key above or equal to @key, else returns NULL.
 * A RCU read-side lock should be held across call to this function and
 * use of its return value.
 */
struct cds_ja_node *cds_ja_lookup_above_equal(struct cds_ja *ja,
		uint64_t key, uint64_t *result_key);

/*
 * cds_ja_add - Add @node at @key, allowing duplicates.
 * @ja: the Judy array.
 * @key: key at which @node should be added.
 * @node: node to add.
 *
 * Returns 0 on success, negative error value on error.
 * A RCU read-side lock should be held across call to this function.
 */
int cds_ja_add(struct cds_ja *ja, uint64_t key,
		struct cds_ja_node *node);

/*
 * cds_ja_add_unique - Add @node at @key, without duplicates.
 * @ja: the Judy array.
 * @key: key at which @node should be added.
 * @node: node to add.
 *
 * Returns @node if successfully added, else returns the already
 * existing node (acts as a RCU lookup).
 * A RCU read-side lock should be held across call to this function and
 * use of its return value.
 */
struct cds_ja_node *cds_ja_add_unique(struct cds_ja *ja, uint64_t key,
		struct cds_ja_node *node);

/*
 * cds_ja_del - Remove @node at @key.
 * @ja: the Judy array.
 * @key: key at which @node is expected.
 * @node: node to remove.
 *
 * Returns 0 on success, negative error value on error.
 * A RCU read-side lock should be held across call to this function.
 */
int cds_ja_del(struct cds_ja *ja, uint64_t key,
		struct cds_ja_node *node);

struct cds_ja *_cds_ja_new(unsigned int key_bits,
		const struct rcu_flavor_struct *flavor);

/*
 * cds_ja_new - Create a Judy array.
 * @key_bits: Number of bits for key.
 *
 * Returns non-NULL pointer on success, else NULL on error. @key_bits
 * needs to be multiple of 8, either: 8, 16, 24, 32, 40, 48, 56, or 64.
 */
static inline
struct cds_ja *cds_ja_new(unsigned int key_bits)
{
	return _cds_ja_new(key_bits, &rcu_flavor);
}

/*
 * cds_ja_destroy - Destroy a Judy array.
 * @ja: the Judy array.
 *
 * Returns 0 on success, negative error value on error.
 * There should be no more concurrent add, delete, nor look-up performed
 * on the Judy array while it is being destroyed (ensured by the caller).
 * RCU read-side lock should _not_ be held when calling this function,
 * however, QSBR threads need to be online.
 */
int cds_ja_destroy(struct cds_ja *ja);

/*
 * cds_ja_for_each_duplicate_rcu: Iterate through duplicates.
 * @pos: struct cds_ja_node *, start of duplicate list and loop cursor.
 *
 * Iterate through duplicates returned by cds_ja_lookup*()
 * This must be done while rcu_read_lock() is held.
 * Receives a struct cds_ja_node * as parameter, which is used as start
 * of duplicate list and loop cursor.
 * _NOT_ safe against node removal within iteration.
 */
#define cds_ja_for_each_duplicate_rcu(pos)					\
	for (; (pos) != NULL; (pos) = rcu_dereference((pos)->next))

/*
 * cds_ja_for_each_duplicate_safe: Iterate through duplicates.
 * @pos: struct cds_ja_node *, start of duplicate list and loop cursor.
 * @p: struct cds_ja_node *, temporary pointer to next.
 *
 * Iterate through duplicates returned by cds_ja_lookup*().
 * Safe against node removal within iteration.
 * This must be done while rcu_read_lock() is held.
 */
#define cds_ja_for_each_duplicate_safe_rcu(pos, p)			\
	for (; (pos) != NULL ?						\
			((p) = rcu_dereference((pos)->next), 1) : 0;	\
			(pos) = (p))

/*
 * cds_ja_for_each_key_rcu: Iterate over all keys in ascending order.
 * @ja: Judy array on which iteration should be done.
 * @key: Key cursor, needs to be a uint64_t.
 * @pos: struct cds_ja_node *, used as loop cursor.
 *
 * Iterate over all keys of a RCU Judy array (_not_ duplicates) in
 * ascending order.
 * This must be done while rcu_read_lock() is held.
 * Safe against node removal during iteration.
 */
#define cds_ja_for_each_key_rcu(ja, key, pos)				\
	for ((key) = 0;							\
		((key) != UINT64_MAX ?					\
			((pos) = cds_ja_lookup_above_equal(ja, key, &(key))) : 0); \
		(key)++)

/*
 * cds_ja_for_each_key_prev_rcu: Iterate over all keys in descending order.
 * @ja: Judy array on which iteration should be done.
 * @key: Key cursor, needs to be a uint64_t.
 * @pos: struct cds_ja_node *, used as loop cursor.
 *
 * Iterate over all keys of a RCU Judy array (_not_ duplicates) in
 * descending order.
 * This must be done while rcu_read_lock() is held.
 * Safe against node removal during iteration.
 */
#define cds_ja_for_each_key_prev_rcu(ja, key, pos)			\
	for ((key) = UINT64_MAX - 1;					\
		((key) != UINT64_MAX ?					\
			((pos) = cds_ja_lookup_below_equal(ja, key, &(key))) : 0); \
		(key)--)

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCUJA_H */
