// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (C) 2018 SUSE.  All rights reserved.
 */

#ifndef BTRFS_BACKREF_CACHE_H
#define BTRFS_BACKREF_CACHE_H

#include "owner-cache.h"

/*
 * present a tree block in the backref cache
 */
struct backref_node {
	struct rb_node rb_node;
	u64 bytenr;

	u64 new_bytenr;
	/* objectid of tree block owner, can be not uptodate */
	u64 owner;
	/* link to pending, changed or detached list */
	struct list_head list;
	/* list of upper level blocks reference this block */
	struct list_head upper;
	/* list of child blocks in the cache */
	struct list_head lower;
	/* NULL if this node is not tree root */
	struct btrfs_root *root;
	/* extent buffer got by COW the block */
	struct extent_buffer *eb;
	/* level of tree block */
	unsigned int level:8;
	/* is the block in non-reference counted tree */
	unsigned int cowonly:1;
	/* 1 if no child node in the cache */
	unsigned int lowest:1;
	/* is the extent buffer locked */
	unsigned int locked:1;
	/* has the block been processed */
	unsigned int processed:1;
	/* have backrefs of this block been checked */
	unsigned int checked:1;
	/*
	 * 1 if corresponding block has been cowed but some upper
	 * level block pointers may not point to the new location
	 */
	unsigned int pending:1;
	/*
	 * 1 if the backref node isn't connected to any other
	 * backref node.
	 */
	unsigned int detached:1;
	/*
	 * The node is mostly readonly at this point.
	 */
	unsigned int complete:1;

	struct owner_cache owners;
	unsigned long in_progress;
};

/*
 * present a block pointer in the backref cache
 */
struct backref_edge {
	struct list_head list[2];
	struct backref_node *node[2];
};

struct backref_cache {
	/* red black tree of all backref nodes in the cache */
	struct rb_root rb_root;
	spinlock_t lock;
	/* for passing backref nodes to btrfs_reloc_cow_block */
	struct backref_node *path[BTRFS_MAX_LEVEL];
	/*
	 * list of blocks that have been cowed but some block
	 * pointers in upper level blocks may not reflect the
	 * new location
	 */
	struct list_head pending[BTRFS_MAX_LEVEL];
	/* list of backref nodes with no child node */
	struct list_head leaves;
	/* list of blocks that have been cowed in current transaction */
	struct list_head changed;
	/* list of detached backref node. */
	struct list_head detached;

	u64 last_trans;

	int nr_nodes;
	int nr_edges;

	struct extent_io_tree processed_blocks;
	struct btrfs_fs_info *fs_info;
};

void backref_cache_init(struct backref_cache *cache,
			struct btrfs_fs_info *fs_info);
void backref_cache_cleanup(struct backref_cache *cache);
struct backref_node *alloc_backref_node(struct backref_cache *cache);
void free_backref_node(struct backref_cache *cache, struct backref_node *node);
struct backref_edge *alloc_backref_edge(struct backref_cache *cache);
void free_backref_edge(struct backref_cache *cache,
		       struct backref_edge *edge);
struct backref_node *backref_tree_search(struct backref_cache *cache,
					 u64 bytenr);

void drop_node_buffer(struct backref_node *node);
void remove_backref_node(struct backref_cache *cache, struct backref_node *node);
void unlock_node_buffer(struct backref_node *node);

void update_backref_node(struct backref_cache *cache,
			 struct backref_node *node, u64 bytenr);
int update_backref_cache(struct btrfs_trans_handle *trans,
			 struct backref_cache *cache);

/* for relocation.c */
#define backref_tree_panic(rb_node, errno, bytenr)			\
	__backref_tree_panic(rb_node, errno, bytenr, __FILE__, __LINE__)
void __backref_tree_panic(struct rb_node *rb_node, int errno, u64 bytenr,
			  const char *filename, unsigned long lineno);
void __mark_block_processed(struct reloc_control *rc, struct backref_node *node);

struct reloc_control;

struct backref_node *build_backref_tree(struct reloc_control *rc,
					struct backref_cache *cache,
					struct btrfs_key *node_key,
					int level, u64 bytenr,
					int search_commit_root);

void backref_cache_collate_owners(struct backref_node *node);

#endif /* BTRFS_BACKREF_CACHE_H */
