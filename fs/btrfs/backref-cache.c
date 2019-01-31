// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (C) 2009 Oracle.  All rights reserved.
 */
#include <linux/sched.h>
#include <linux/pagemap.h>
#include <linux/writeback.h>
#include <linux/blkdev.h>
#include <linux/rbtree.h>
#include <linux/slab.h>
#include "ctree.h"
#include "disk-io.h"
#include "transaction.h"
#include "volumes.h"
#include "locking.h"
#include "btrfs_inode.h"
#include "async-thread.h"
#include "free-space-cache.h"
#include "inode-map.h"
#include "qgroup.h"
#include "print-tree.h"
#include "relocation.h"

#include "backref-cache.h"

static void mark_block_processed(struct reloc_control *rc,
				 struct btrfs_fs_info *fs_info,
				 struct extent_io_tree *processed_blocks,
				 struct backref_node *node);

void __backref_tree_panic(struct rb_node *rb_node, int errno, u64 bytenr,
			  const char *filename, unsigned long lineno)
{

	struct btrfs_fs_info *fs_info = NULL;
	struct backref_node *bnode = rb_entry(rb_node, struct backref_node,
					      rb_node);
	if (bnode->root)
		fs_info = bnode->root->fs_info;
	btrfs_panic(fs_info, errno,
		    "%s:%lu Inconsistency in backref cache found at offset %llu",
		    filename, lineno, bytenr);
}

void backref_cache_init(struct backref_cache *cache,
			struct btrfs_fs_info *fs_info)
{
	int i;
	cache->rb_root = RB_ROOT;
	spin_lock_init(&cache->lock);
	for (i = 0; i < BTRFS_MAX_LEVEL; i++) {
		INIT_LIST_HEAD(&cache->pending[i]);
		cache->path[i] = NULL;
	}
	INIT_LIST_HEAD(&cache->changed);
	INIT_LIST_HEAD(&cache->detached);
	INIT_LIST_HEAD(&cache->leaves);
	cache->last_trans = 0ULL;
	cache->nr_nodes = cache->nr_edges = 0;
	extent_io_tree_init(&cache->processed_blocks, NULL);
	cache->fs_info = fs_info;
}

void backref_cache_cleanup(struct backref_cache *cache)
{
	struct backref_node *node;
	int i;

	while (!list_empty(&cache->detached)) {
		node = list_entry(cache->detached.next,
				  struct backref_node, list);
		remove_backref_node(cache, node);
	}

	while (!list_empty(&cache->leaves)) {
		node = list_entry(cache->leaves.next,
				  struct backref_node, lower);
		remove_backref_node(cache, node);
	}

	cache->last_trans = 0;

	for (i = 0; i < BTRFS_MAX_LEVEL; i++)
		ASSERT(list_empty(&cache->pending[i]));
	ASSERT(list_empty(&cache->changed));
	ASSERT(list_empty(&cache->detached));
	ASSERT(RB_EMPTY_ROOT(&cache->rb_root));
	ASSERT(!cache->nr_nodes);
	ASSERT(!cache->nr_edges);
}

static void wait_on_backref(struct backref_node *backref)
{
	int ret;
	ret = wait_on_bit_io(&backref->in_progress, 0, TASK_UNINTERRUPTIBLE);
	BUG_ON(ret);/* We should never get here */
}

struct backref_node *backref_tree_search(struct backref_cache *cache,
					 u64 bytenr)
{
	struct backref_node *backref;
	struct rb_node *node;

	spin_lock(&cache->lock);
	node = tree_search(&cache->rb_root, bytenr);
	spin_unlock(&cache->lock);
	if (node) {
		backref = rb_entry(node, struct backref_node, rb_node);
		wait_on_backref(backref);
		return backref;
	}
	return NULL;
}

struct backref_node *alloc_backref_node(struct backref_cache *cache)
{
	struct backref_node *node;

	node = kzalloc(sizeof(*node), GFP_NOFS);
	if (node) {
		INIT_LIST_HEAD(&node->list);
		INIT_LIST_HEAD(&node->upper);
		INIT_LIST_HEAD(&node->lower);
		RB_CLEAR_NODE(&node->rb_node);
		owner_cache_init(&node->owners);
		set_bit(0, &node->in_progress);
		cache->nr_nodes++;
	}
	return node;
}

struct backref_node *backref_tree_insert(struct backref_cache *cache,
					 struct backref_node *cur)
{
	struct backref_node *backref;
	struct rb_node *node;

	spin_lock(&cache->lock);
	node = tree_search(&cache->rb_root, cur->bytenr);
	if (node) {
		if (node == &cur->rb_node) {
			spin_unlock(&cache->lock);
			return cur;
		}
		spin_unlock(&cache->lock);

		free_backref_node(cache, cur);

		backref = rb_entry(node, struct backref_node, rb_node);
		wait_on_backref(backref);
		return backref;
	}
	tree_insert(&cache->rb_root, cur->bytenr, &cur->rb_node);
	spin_unlock(&cache->lock);

	return cur;
}

struct backref_node *backref_tree_search_insert(struct backref_cache *cache,
						u64 bytenr, int level)
{
	struct backref_node *insert = NULL;
	struct backref_node *backref;
	struct rb_node *node;

retry:
	spin_lock(&cache->lock);
	node = tree_search(&cache->rb_root, bytenr);
	if (!node) {
		if (insert) {
			tree_insert(&cache->rb_root, insert->bytenr,
				    &insert->rb_node);
			spin_unlock(&cache->lock);
			return insert;
		}
		spin_unlock(&cache->lock);

		insert = alloc_backref_node(cache);
		if (!insert)
			return NULL;

		insert->bytenr = bytenr;
		insert->level = level;
		goto retry;
	}
	spin_unlock(&cache->lock);

	free_backref_node(cache, insert);

	backref = rb_entry(node, struct backref_node, rb_node);
	wait_on_backref(backref);

	return backref;
}

static void maybe_unlock_backref(struct backref_node *node)
{
	/*
	 * If we always wait on the lock bit, and
	 * the bit is never set again after being cleared, then a set
	 * bit here means we own the lock
	 */
	if (test_bit(0, &node->in_progress)) {
		node->complete = 1;
		clear_and_wake_up_bit(0, &node->in_progress);
	}
}

void free_backref_node(struct backref_cache *cache, struct backref_node *node)
{
	if (node) {
		cache->nr_nodes--;
		kfree(node);
	}
}

struct backref_edge *alloc_backref_edge(struct backref_cache *cache)
{
	struct backref_edge *edge;

	edge = kzalloc(sizeof(*edge), GFP_NOFS);
	if (edge)
		cache->nr_edges++;
	return edge;
}

void free_backref_edge(struct backref_cache *cache, struct backref_edge *edge)
{
	if (edge) {
		cache->nr_edges--;
		kfree(edge);
	}
}

void unlock_node_buffer(struct backref_node *node)
{
	if (node->locked) {
		btrfs_tree_unlock(node->eb);
		node->locked = 0;
	}
}

void drop_node_buffer(struct backref_node *node)
{
	if (node->eb) {
		unlock_node_buffer(node);
		free_extent_buffer(node->eb);
		node->eb = NULL;
	}
}

static void drop_backref_node(struct backref_cache *tree,
			      struct backref_node *node)
{
	BUG_ON(!list_empty(&node->upper));

	drop_node_buffer(node);
	list_del(&node->list);
	list_del(&node->lower);
	if (!RB_EMPTY_NODE(&node->rb_node))
		rb_erase(&node->rb_node, &tree->rb_root);
	owner_cache_destroy(&node->owners);
	free_backref_node(tree, node);
}

/*
 * remove a backref node from the backref cache
 */
void remove_backref_node(struct backref_cache *cache, struct backref_node *node)
{
	struct backref_node *upper;
	struct backref_edge *edge;

	if (!node)
		return;

	BUG_ON(!node->lowest && !node->detached);
	while (!list_empty(&node->upper)) {
		edge = list_entry(node->upper.next, struct backref_edge,
				  list[LOWER]);
		upper = edge->node[UPPER];
		list_del(&edge->list[LOWER]);
		list_del(&edge->list[UPPER]);
		free_backref_edge(cache, edge);

		if (RB_EMPTY_NODE(&upper->rb_node)) {
			BUG_ON(!list_empty(&node->upper));
			drop_backref_node(cache, node);
			node = upper;
			node->lowest = 1;
			continue;
		}
		/*
		 * add the node to leaf node list if no other
		 * child block cached.
		 */
		if (list_empty(&upper->lower)) {
			list_add_tail(&upper->lower, &cache->leaves);
			upper->lowest = 1;
		}
	}

	drop_backref_node(cache, node);
}

void update_backref_node(struct backref_cache *cache,
			 struct backref_node *node, u64 bytenr)
{
	struct rb_node *rb_node;
	rb_erase(&node->rb_node, &cache->rb_root);
	node->bytenr = bytenr;
	rb_node = tree_insert(&cache->rb_root, node->bytenr, &node->rb_node);
	if (rb_node)
		backref_tree_panic(rb_node, -EEXIST, bytenr);
}
/*
 * update backref cache after a transaction commit
 */
int update_backref_cache(struct btrfs_trans_handle *trans,
			 struct backref_cache *cache)
{
	struct backref_node *node;
	int level = 0;

	if (cache->last_trans == 0) {
		cache->last_trans = trans->transid;
		return 0;
	}

	if (cache->last_trans == trans->transid)
		return 0;

	/*
	 * detached nodes are used to avoid unnecessary backref
	 * lookup. transaction commit changes the extent tree.
	 * so the detached nodes are no longer useful.
	 */
	while (!list_empty(&cache->detached)) {
		node = list_entry(cache->detached.next,
				  struct backref_node, list);
		remove_backref_node(cache, node);
	}

	while (!list_empty(&cache->changed)) {
		node = list_entry(cache->changed.next,
				  struct backref_node, list);
		list_del_init(&node->list);
		BUG_ON(node->pending);
		update_backref_node(cache, node, node->new_bytenr);
	}

	/*
	 * some nodes can be left in the pending list if there were
	 * errors during processing the pending nodes.
	 */
	for (level = 0; level < BTRFS_MAX_LEVEL; level++) {
		list_for_each_entry(node, &cache->pending[level], list) {
			BUG_ON(!node->pending);
			if (node->bytenr == node->new_bytenr)
				continue;
			update_backref_node(cache, node, node->new_bytenr);
		}
	}

	cache->last_trans = 0;
	return 1;
}


static int should_ignore_root(struct btrfs_root *root)
{
	struct btrfs_root *reloc_root;

	if (!test_bit(BTRFS_ROOT_REF_COWS, &root->state))
		return 0;

	if (test_bit(BTRFS_FS_QUOTA_ENABLED, &root->fs_info->flags))
		return 0;

	reloc_root = root->reloc_root;
	if (!reloc_root)
		return 0;

	if (btrfs_root_last_snapshot(&reloc_root->root_item) ==
	    root->fs_info->running_transaction->transid - 1)
		return 0;
	/*
	 * if there is reloc tree and it was created in previous
	 * transaction backref lookup can find the reloc tree,
	 * so backref node for the fs tree root is useless for
	 * relocation.
	 */
	return 1;
}
/*
 * find reloc tree by address of tree root
 */
static struct btrfs_root *find_reloc_root(struct reloc_control *rc,
					  u64 bytenr)
{
	struct rb_node *rb_node;
	struct mapping_node *node;
	struct btrfs_root *root = NULL;

	spin_lock(&rc->reloc_root_tree.lock);
	rb_node = tree_search(&rc->reloc_root_tree.rb_root, bytenr);
	if (rb_node) {
		node = rb_entry(rb_node, struct mapping_node, rb_node);
		root = (struct btrfs_root *)node->data;
	}
	spin_unlock(&rc->reloc_root_tree.lock);
	return root;
}

#ifdef BTRFS_COMPAT_EXTENT_TREE_V0
static noinline_for_stack
struct btrfs_root *find_tree_root(struct btrfs_fs_info *fs_info,
				  struct extent_buffer *leaf,
				  struct btrfs_extent_ref_v0 *ref0)
{
	struct btrfs_root *root;
	u64 root_objectid = btrfs_ref_root_v0(leaf, ref0);
	u64 generation = btrfs_ref_generation_v0(leaf, ref0);

	BUG_ON(root_objectid == BTRFS_TREE_RELOC_OBJECTID);

	root = read_fs_root(fs_info, root_objectid);
	BUG_ON(IS_ERR(root));

	if (test_bit(BTRFS_ROOT_REF_COWS, &root->state) &&
	    generation != btrfs_root_generation(&root->root_item))
		return NULL;

	return root;
}
#endif

static noinline_for_stack
int find_inline_backref(struct extent_buffer *leaf, int slot,
			unsigned long *ptr, unsigned long *end)
{
	struct btrfs_key key;
	struct btrfs_extent_item *ei;
	struct btrfs_tree_block_info *bi;
	u32 item_size;

	btrfs_item_key_to_cpu(leaf, &key, slot);

	item_size = btrfs_item_size_nr(leaf, slot);
#ifdef BTRFS_COMPAT_EXTENT_TREE_V0
	if (item_size < sizeof(*ei)) {
		WARN_ON(item_size != sizeof(struct btrfs_extent_item_v0));
		return 1;
	}
#endif
	ei = btrfs_item_ptr(leaf, slot, struct btrfs_extent_item);
	WARN_ON(!(btrfs_extent_flags(leaf, ei) &
		  BTRFS_EXTENT_FLAG_TREE_BLOCK));

	if (key.type == BTRFS_EXTENT_ITEM_KEY &&
	    item_size <= sizeof(*ei) + sizeof(*bi)) {
		WARN_ON(item_size < sizeof(*ei) + sizeof(*bi));
		return 1;
	}
	if (key.type == BTRFS_METADATA_ITEM_KEY &&
	    item_size <= sizeof(*ei)) {
		WARN_ON(item_size < sizeof(*ei));
		return 1;
	}

	if (key.type == BTRFS_EXTENT_ITEM_KEY) {
		bi = (struct btrfs_tree_block_info *)(ei + 1);
		*ptr = (unsigned long)(bi + 1);
	} else {
		*ptr = (unsigned long)(ei + 1);
	}
	*end = (unsigned long)ei + item_size;
	return 0;
}

#define SEARCH_COMPLETE	1
#define SEARCH_NEXT	2
static int find_next_ref(struct btrfs_root *extent_root, u64 cur_bytenr,
			 struct btrfs_path *path, unsigned long *ptr,
			 unsigned long *end, struct btrfs_key *key, bool exist)
{
	struct extent_buffer *eb = path->nodes[0];
	int ret;

	if (*ptr >= *end) {
		if (path->slots[0] >= btrfs_header_nritems(eb)) {
			ret = btrfs_next_leaf(extent_root, path);
			if (ret < 0)
				goto out;
			if (ret > 0)
				return SEARCH_COMPLETE;
			eb = path->nodes[0];
		}

		btrfs_item_key_to_cpu(eb, key, path->slots[0]);
		if (key->objectid != cur_bytenr) {
			WARN_ON(exist);
			return SEARCH_COMPLETE;
		}

		if (key->type == BTRFS_EXTENT_ITEM_KEY ||
		    key->type == BTRFS_METADATA_ITEM_KEY) {
			ret = find_inline_backref(eb, path->slots[0],
						  ptr, end);
			if (ret)
				return SEARCH_NEXT;
		}
	}

	if (*ptr < *end) {
		/* update key for inline back ref */
		struct btrfs_extent_inline_ref *iref;
		int type;
		iref = (struct btrfs_extent_inline_ref *)(*ptr);
		type = btrfs_get_extent_inline_ref_type(eb, iref,
							BTRFS_REF_TYPE_BLOCK);
		if (type == BTRFS_REF_TYPE_INVALID) {
			ret = -EINVAL;
			goto out;
		}
		key->type = type;
		key->offset = btrfs_extent_inline_ref_offset(eb, iref);

		WARN_ON(key->type != BTRFS_TREE_BLOCK_REF_KEY &&
			key->type != BTRFS_SHARED_BLOCK_REF_KEY);
	}
	ret = 0;
out:
	return ret;
}

/*
 * build backref tree for a given tree block. root of the backref tree
 * corresponds the tree block, leaves of the backref tree correspond
 * roots of b-trees that reference the tree block.
 *
 * the basic idea of this function is check backrefs of a given block
 * to find upper level blocks that reference the block, and then check
 * backrefs of these upper level blocks recursively. the recursion stop
 * when tree root is reached or backrefs for the block is cached.
 *
 * NOTE: if we find backrefs for a block are cached, we know backrefs
 * for all upper level blocks that directly/indirectly reference the
 * block are also cached.
 */
noinline_for_stack
struct backref_node *build_backref_tree(struct reloc_control *rc,
					struct backref_cache *cache,
					struct btrfs_key *node_key,
					int level, u64 bytenr,
					int search_commit_root)
{
	struct btrfs_path *path1;
	struct btrfs_path *path2;
	struct extent_buffer *eb;
	struct btrfs_root *root, *extent_root;
	struct backref_node *cur;
	struct backref_node *upper;
	struct backref_node *lower;
	struct backref_node *node = NULL;
	struct backref_node *exist = NULL;
	struct backref_edge *edge;
	struct rb_node *rb_node;
	struct btrfs_key key;
	struct extent_io_tree *processed_blocks;
	struct btrfs_fs_info *fs_info = cache->fs_info;
	unsigned long end;
	unsigned long ptr;
	LIST_HEAD(list);
	LIST_HEAD(useless);
	int cowonly;
	int ret;
	int err = 0;
	bool need_check = true;
	int keep_nodes = 0;

	extent_root = fs_info->extent_root;
	if (rc) {
		processed_blocks = &rc->processed_blocks;
	} else {
		processed_blocks = &cache->processed_blocks;
		keep_nodes = 1;
	}

	path1 = btrfs_alloc_path();
	path2 = btrfs_alloc_path();
	if (!path1 || !path2) {
		err = -ENOMEM;
		goto out;
	}
	path1->reada = READA_FORWARD;
	path2->reada = READA_FORWARD;

	node = alloc_backref_node(cache);
	if (!node) {
		err = -ENOMEM;
		goto out;
	}

	ASSERT(!backref_tree_search(cache, bytenr));

	node->bytenr = bytenr;
	node->level = level;
	node->lowest = 1;
	cur = node;
	printk("backref: build tree for bytenr %llu level %d\n", node->bytenr,
	       level);
again:
	end = 0;
	ptr = 0;
	key.objectid = cur->bytenr;
	key.type = BTRFS_METADATA_ITEM_KEY;
	key.offset = (u64)-1;

	cur = backref_tree_insert(cache, cur);
	/* Do we make node=cur here? */
	if (cur->complete) {
		/*
		 * We have already cache backrefs for this block and
		 * refs of those refs, etc
		 */
		goto next_block;
	}

	path1->search_commit_root = search_commit_root;
	path1->skip_locking = search_commit_root;
	ret = btrfs_search_slot(NULL, extent_root, &key, path1, 0, 0);
	if (ret < 0) {
		err = ret;
		goto out;
	}
	ASSERT(ret);
	ASSERT(path1->slots[0]);

	path1->slots[0]--;

	WARN_ON(!keep_nodes && cur->checked);
	if (!list_empty(&cur->upper)) {
		/*
		 * the backref was added previously when processing
		 * backref of type BTRFS_TREE_BLOCK_REF_KEY
		 */
		ASSERT(list_is_singular(&cur->upper));
		edge = list_entry(cur->upper.next, struct backref_edge,
				  list[LOWER]);
		ASSERT(list_empty(&edge->list[UPPER]));
		exist = edge->node[UPPER];
		/*
		 * add the upper level block to pending list if we need
		 * check its backrefs
		 */
		if (!exist->checked)
			list_add_tail(&edge->list[UPPER], &list);
	} else {
		exist = NULL;
	}

	printk("backref: search slot for key (%llu %d %lld) exist %p\n",
	       key.objectid, key.type, key.offset, exist);

	while (1) {
		cond_resched();

		ret = find_next_ref(extent_root, cur->bytenr, path1, &ptr, &end,
				    &key, exist != NULL);
		if (ret < 0) {
			err = ret;
			goto out;
		}
		eb = path1->nodes[0];

		if (ret == SEARCH_COMPLETE)
			break;
		else if (ret == SEARCH_NEXT)
			goto next;

		if (exist &&
		    ((key.type == BTRFS_TREE_BLOCK_REF_KEY &&
		      exist->owner == key.offset) ||
		     (key.type == BTRFS_SHARED_BLOCK_REF_KEY &&
		      exist->bytenr == key.offset))) {
			exist = NULL;
			goto next;
		}

#ifdef BTRFS_COMPAT_EXTENT_TREE_V0
		if (key.type == BTRFS_SHARED_BLOCK_REF_KEY ||
		    key.type == BTRFS_EXTENT_REF_V0_KEY) {
			if (key.type == BTRFS_EXTENT_REF_V0_KEY) {
				struct btrfs_extent_ref_v0 *ref0;
				ref0 = btrfs_item_ptr(eb, path1->slots[0],
						struct btrfs_extent_ref_v0);
				if (key.objectid == key.offset) {
					root = find_tree_root(fs_info, eb,
							      ref0);
					if (root && !should_ignore_root(root))
						cur->root = root;
					else if (!keep_nodes)
						list_add(&cur->list, &useless);
					break;
				}
				if (!cur-complete &&
				    is_cowonly_root(btrfs_ref_root_v0(eb,
								      ref0)))
					cur->cowonly = 1;
			}
#else
		ASSERT(key.type != BTRFS_EXTENT_REF_V0_KEY);
		if (key.type == BTRFS_SHARED_BLOCK_REF_KEY) {
#endif
			if (key.objectid == key.offset) {
				/*
				 * only root blocks of reloc trees use
				 * backref of this type.
				 */
				if (!keep_nodes) {
					root = find_reloc_root(rc, cur->bytenr);
					ASSERT(root);
					if (!cur->complete)
						cur->root = root;
				}
				break;
			}

			edge = alloc_backref_edge(cache);
			if (!edge) {
				err = -ENOMEM;
				goto out;
			}
			upper = backref_tree_search_insert(cache, key.offset,
							   cur->level + 1);
			if (!upper) {
				err = -ENOMEM;
				goto out;
			}
			if (!upper->complete) {
				/*
				 * We have allocated the node, add it
				 * to our list so that we check it
				 * later
				 */
				list_add_tail(&edge->list[UPPER], &list);
			} else {
				rb_node = &upper->rb_node;
				ASSERT(upper->checked);
				INIT_LIST_HEAD(&edge->list[UPPER]);
			}

			edge->node[LOWER] = cur;
			edge->node[UPPER] = upper;
			spin_lock(&cache->lock);
			list_add_tail(&edge->list[LOWER], &cur->upper);
			spin_unlock(&cache->lock);
			goto next;
		} else if (key.type != BTRFS_TREE_BLOCK_REF_KEY) {
			goto next;
		}

		/* key.type == BTRFS_TREE_BLOCK_REF_KEY */
		root = read_fs_root(fs_info, key.offset);
		if (IS_ERR(root)) {
			err = PTR_ERR(root);
			goto out;
		}

		printk("backref: read_fs_root (ret %p %llu) item key (%llu %d %lld) "
		       "should_ignore: %d\n",
		       root, root ? root->objectid : 0ULL, key.objectid, key.type, key.offset,
		       should_ignore_root(root));

		if (!cur->complete && !test_bit(BTRFS_ROOT_REF_COWS, &root->state))
			cur->cowonly = 1;

		if (btrfs_root_level(&root->root_item) == cur->level) {
			/* tree root */
			if (search_commit_root)
				ASSERT(root->commit_root->start == cur->bytenr);
			else
				ASSERT(root->node->start == cur->bytenr);
			if (!cur->complete) {
				if (should_ignore_root(root))
					list_add(&cur->list, &useless);
				else
					cur->root = root;
			}
			break;
		}

		level = cur->level + 1;

		/*
		 * searching the tree to find upper level blocks
		 * reference the block.
		 */
		path2->search_commit_root = search_commit_root;
		path2->skip_locking = search_commit_root;
		path2->lowest_level = level;
		ret = btrfs_search_slot(NULL, root, node_key, path2, 0, 0);
		path2->lowest_level = 0;
		if (ret < 0) {
			err = ret;
			goto out;
		}
		if (ret > 0 && path2->slots[level] > 0)
			path2->slots[level]--;

		printk("backref: 2nd search found node_key (%llu %d %lld)\n",
		       node_key->objectid, node_key->type, node_key->offset);

		eb = path2->nodes[level];
		if (btrfs_node_blockptr(eb, path2->slots[level]) !=
		    cur->bytenr) {
			btrfs_err(root->fs_info,
	"couldn't find block (%llu) (level %d) in tree (%llu) with key (%llu %u %llu)",
				  cur->bytenr, level - 1, root->objectid,
				  node_key->objectid, node_key->type,
				  node_key->offset);
			err = -ENOENT;
			goto out;
		}
		lower = cur;
		need_check = true;
		for (; level < BTRFS_MAX_LEVEL; level++) {
			if (!path2->nodes[level]) {
				if (search_commit_root)
					ASSERT(root->commit_root->start == lower->bytenr);
				else
					ASSERT(root->node->start == lower->bytenr);
				if (!lower->complete) {
					if (should_ignore_root(root))
						list_add(&lower->list, &useless);
					else
						lower->root = root;
					break;
				}
			}

			eb = path2->nodes[level];
			upper = backref_tree_search_insert(cache, eb->start,
							   lower->level + 1);
			if (!upper) {
				err = -ENOMEM;
				goto out;
			}

			if (upper->complete) {
				rb_node = &upper->rb_node;
				ASSERT(upper->checked);
				/* XXX: What to do here? */
				if (!upper->owner)
					upper->owner = btrfs_header_owner(eb);
				break;
			}

			edge = alloc_backref_edge(cache);
			if (!edge) {
				err = -ENOMEM;
				goto out;
			}

			upper->owner = btrfs_header_owner(eb);
			if (!test_bit(BTRFS_ROOT_REF_COWS,
				      &root->state))
				upper->cowonly = 1;

			/*
			 * if we know the block isn't shared
			 * we can void checking its backrefs.
			 */
			if (btrfs_block_can_be_shared(root, eb))
				upper->checked = 0;
			else
				upper->checked = 1;

			/*
			 * add the block to pending list if we
			 * need check its backrefs, we only do this once
			 * while walking up a tree as we will catch
			 * anything else later on.
			 */
			if (!upper->checked && need_check) {
				need_check = false;
				list_add_tail(&edge->list[UPPER],
					      &list);
			} else {
				if (upper->checked)
					need_check = true;
				INIT_LIST_HEAD(&edge->list[UPPER]);
			}

			list_add_tail(&edge->list[LOWER], &lower->upper);
			edge->node[LOWER] = lower;
			edge->node[UPPER] = upper;
			if (rb_node)
				break;
			lower = upper;
			upper = NULL;

		}
		btrfs_release_path(path2);
next:
		if (ptr < end) {
			ptr += btrfs_extent_inline_ref_size(key.type);
			if (ptr >= end) {
				WARN_ON(ptr > end);
				ptr = 0;
				end = 0;
			}
		}
		if (ptr >= end)
			path1->slots[0]++;
	}
	btrfs_release_path(path1);

	cur->checked = 1;
	WARN_ON(exist);

next_block:
	/* the pending list isn't empty, take the first block to process */
	while (!list_empty(&list)) {
		edge = list_entry(list.next, struct backref_edge, list[UPPER]);
		list_del_init(&edge->list[UPPER]);
		cur = edge->node[UPPER];
		WARN_ON(cur->checked || cur->complete);
		goto again;
	}

	/*
	 * everything goes well, connect backref nodes and insert backref nodes
	 * into the cache.
	 */
	ASSERT(node->checked);
	cowonly = node->cowonly;
	if (!cowonly) {
		node = backref_tree_insert(cache, node);
		list_add_tail(&node->lower, &cache->leaves);
	}

	list_for_each_entry(edge, &node->upper, list[LOWER])
		list_add_tail(&edge->list[UPPER], &list);

	while (!list_empty(&list)) {
		edge = list_entry(list.next, struct backref_edge, list[UPPER]);
		list_del_init(&edge->list[UPPER]);
		upper = edge->node[UPPER];
		BUG_ON(upper->complete);
		if (upper->detached) {
			list_del(&edge->list[LOWER]);
			lower = edge->node[LOWER];
			free_backref_edge(cache, edge);
			if (list_empty(&lower->upper))
				list_add(&lower->list, &useless);
			goto unlock_next;
		}

		if (!RB_EMPTY_NODE(&upper->rb_node)) {
			if (upper->lowest) {
				list_del_init(&upper->lower);
				upper->lowest = 0;
			}

			list_add_tail(&edge->list[UPPER], &upper->lower);
			goto unlock_next;
		}

		if (!upper->checked) {
			/*
			 * Still want to blow up for developers since this is a
			 * logic bug.
			 */
			ASSERT(0);
			err = -EINVAL;
			goto out;
		}
		if (cowonly != upper->cowonly) {
			ASSERT(0);
			err = -EINVAL;
			goto out;
		}

		list_add_tail(&edge->list[UPPER], &upper->lower);

		list_for_each_entry(edge, &upper->upper, list[LOWER])
			list_add_tail(&edge->list[UPPER], &list);
unlock_next:
		maybe_unlock_backref(upper);
	}
	maybe_unlock_backref(node);

	/*
	 * process useless backref nodes. backref nodes for tree leaves
	 * are deleted from the cache. backref nodes for upper level
	 * tree blocks are left in the cache to avoid unnecessary backref
	 * lookup.
	 */
	while (!list_empty(&useless)) {
		BUG_ON(keep_nodes);
		upper = list_entry(useless.next, struct backref_node, list);
		list_del_init(&upper->list);
		ASSERT(list_empty(&upper->upper));
		if (upper == node)
			node = NULL;
		if (upper->lowest) {
			list_del_init(&upper->lower);
			upper->lowest = 0;
		}
		while (!list_empty(&upper->lower)) {
			edge = list_entry(upper->lower.next,
					  struct backref_edge, list[UPPER]);
			list_del(&edge->list[UPPER]);
			list_del(&edge->list[LOWER]);
			lower = edge->node[LOWER];
			free_backref_edge(cache, edge);

			if (list_empty(&lower->upper))
				list_add(&lower->list, &useless);
		}
		mark_block_processed(rc, fs_info, processed_blocks, upper);
		if (upper->level > 0) {
			list_add(&upper->list, &cache->detached);
			upper->detached = 1;
		} else {
			rb_erase(&upper->rb_node, &cache->rb_root);
			free_backref_node(cache, upper);
		}
	}
out:
	btrfs_free_path(path1);
	btrfs_free_path(path2);
	if (err) {
		while (!list_empty(&useless)) {
			lower = list_entry(useless.next,
					   struct backref_node, list);
			list_del_init(&lower->list);
		}
		while (!list_empty(&list)) {
			edge = list_first_entry(&list, struct backref_edge,
						list[UPPER]);
			list_del(&edge->list[UPPER]);
			list_del(&edge->list[LOWER]);
			lower = edge->node[LOWER];
			upper = edge->node[UPPER];
			free_backref_edge(cache, edge);

			/*
			 * Lower is no longer linked to any upper backref nodes
			 * and isn't in the cache, we can free it ourselves.
			 */
			if (list_empty(&lower->upper) &&
			    RB_EMPTY_NODE(&lower->rb_node))
				list_add(&lower->list, &useless);

			if (!RB_EMPTY_NODE(&upper->rb_node))
				continue;

			/* Add this guy's upper edges to the list to process */
			list_for_each_entry(edge, &upper->upper, list[LOWER])
				list_add_tail(&edge->list[UPPER], &list);
			if (list_empty(&upper->upper))
				list_add(&upper->list, &useless);
		}

		while (!list_empty(&useless)) {
			lower = list_entry(useless.next,
					   struct backref_node, list);
			list_del_init(&lower->list);
			if (lower == node)
				node = NULL;
			free_backref_node(cache, lower);
		}

		free_backref_node(cache, node);
		return ERR_PTR(err);
	}
	ASSERT(!node || !node->detached);
	return node;
}

static void mark_block_processed(struct reloc_control *rc,
				 struct btrfs_fs_info *fs_info,
				 struct extent_io_tree *processed_blocks,
				 struct backref_node *node)
{
	u32 blocksize = fs_info->nodesize;
	u64 bytenr = node->bytenr;

	if (!rc || node->level == 0 ||
	    in_block_group(node->bytenr, rc->block_group))
		set_extent_bits(processed_blocks, bytenr,
				bytenr + blocksize - 1,	EXTENT_DIRTY);
	node->processed = 1;
}

void __mark_block_processed(struct reloc_control *rc, struct backref_node *node)
{
	mark_block_processed(rc, rc->extent_root->fs_info,
			     &rc->processed_blocks, node);
}

void backref_cache_collate_owners(struct backref_node *node)
{
	struct backref_edge *edge;

	printk("Collate: bytenr %llu  RB_EMPTY_ROOT: %d  node->root: %p\n",
	       node->bytenr,!!RB_EMPTY_ROOT(&node->owners.root), node->root);
	if (!RB_EMPTY_ROOT(&node->owners.root)) {
		return;
	}

	list_for_each_entry(edge, &node->upper, list[LOWER]) {
		backref_cache_collate_owners(edge->node[UPPER]);
		owner_cache_merge(&edge->node[UPPER]->owners, &node->owners);
	}

	if (node->root) {
		int ret;
		u64 root = node->root->objectid;
		ret = owner_cache_add_root(&node->owners, root);
		BUG_ON(ret);
	}
}
