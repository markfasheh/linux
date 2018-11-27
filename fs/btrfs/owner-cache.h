// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (C) 2018 SUSE.  All rights reserved.
 */

#ifndef _OWNER_CACHE_H_
#define _OWNER_CACHE_H_

#include <linux/kernel.h>
#include <linux/rbtree.h>
#include <linux/bitops.h>

struct backref_node;

struct owner_cache {
	struct rb_root root;
	u64 refs;
};

static inline void owner_cache_init(struct owner_cache *cache)
{
	cache->root = RB_ROOT;
	cache->refs = 0;
}

#define DECLARE_BITMAP(name,bits)		\
        unsigned long name[BITS_TO_LONGS(bits)]

#define OWNER_CACHE_SIZE 256
#define OWNER_CACHE_INDEX_BITS	8
#define OWNER_CACHE_INDEX(x)	(x >> OWNER_CACHE_INDEX_BITS)
#define OWNER_CACHE_BIT(x)	(x & 255)

/* 64 bytes, covers a range of 256 roots */
struct owner_cache_node
{
	struct rb_node node;
	u64 index;
	DECLARE_BITMAP(bitmap, 256);
};

static inline struct owner_cache_node *to_cache_node(struct rb_node *node)
{
	return container_of(node, struct owner_cache_node, node);
}

int owner_cache_add_root(struct owner_cache *cache, u64 root);
int owner_cache_merge(struct owner_cache *src, struct owner_cache *dst);
//void owner_cache_dump(struct owner_cache *cache);
void owner_cache_destroy(struct owner_cache *cache);
int owner_cache_iterate_owners(struct owner_cache *cache,
			       int (*callback)(struct owner_cache *cache,
					       u64 root, void *data),
			       void *data);

bool owner_cache_compare(struct owner_cache *cache1,
			 struct owner_cache *cache2);
#endif /* _OWNER_CACHE_H_ */
