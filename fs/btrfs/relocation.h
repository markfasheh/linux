// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (C) 2018 SUSE.  All rights reserved.
 */

#ifndef BTRFS_RELOCATION_H
#define BTRFS_RELOCATION_H

#include "backref-cache.h"

#define LOWER	0
#define UPPER	1
#define RELOCATION_RESERVED_NODES	256

/*
 * map address of tree root to tree
 */
struct mapping_node {
	struct rb_node rb_node;
	u64 bytenr;
	void *data;
};

struct mapping_tree {
	struct rb_root rb_root;
	spinlock_t lock;
};

#define MAX_EXTENTS 128

struct file_extent_cluster {
	u64 start;
	u64 end;
	u64 boundary[MAX_EXTENTS];
	unsigned int nr;
};

struct reloc_control {
	/* block group to relocate */
	struct btrfs_block_group_cache *block_group;
	/* extent tree */
	struct btrfs_root *extent_root;
	/* inode for moving data */
	struct inode *data_inode;

	struct btrfs_block_rsv *block_rsv;

	struct backref_cache backref_cache;

	struct file_extent_cluster cluster;
	/* tree blocks have been processed */
	struct extent_io_tree processed_blocks;
	/* map start of tree root to corresponding reloc tree */
	struct mapping_tree reloc_root_tree;
	/* list of reloc trees */
	struct list_head reloc_roots;
	/* size of metadata reservation for merging reloc trees */
	u64 merging_rsv_size;
	/* size of relocated tree nodes */
	u64 nodes_relocated;
	/* reserved size for block group relocation*/
	u64 reserved_bytes;

	u64 search_start;
	u64 extents_found;

	unsigned int stage:8;
	unsigned int create_reloc_tree:1;
	unsigned int merge_reloc_tree:1;
	unsigned int found_file_extent:1;
};

/* stages of data relocation */
#define MOVE_DATA_EXTENTS	0
#define UPDATE_DATA_PTRS	1

/* for backref-cache.c */
int is_cowonly_root(u64 root_objectid);
struct btrfs_root *read_fs_root(struct btrfs_fs_info *fs_info,
				u64 root_objectid);
int in_block_group(u64 bytenr, struct btrfs_block_group_cache *block_group);

struct rb_node *tree_insert(struct rb_root *root, u64 bytenr,
			    struct rb_node *node);
struct rb_node *tree_search(struct rb_root *root, u64 bytenr);

#endif /* BTRFS_RELOCATION_H */
