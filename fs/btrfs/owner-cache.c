// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (C) 2018 SUSE.  All rights reserved.
 */
#include <linux/pagemap.h>
#include <linux/rbtree.h>
#include <linux/slab.h>

#include "owner-cache.h"

static struct owner_cache_node *
find_or_create_cache_node(struct owner_cache *cache, u64 index)
{
	struct owner_cache_node *node;
	struct rb_node **p = &cache->root.rb_node;
	struct rb_node *parent = NULL;

	while(*p) {
		parent = *p;
		node = to_cache_node(parent);

		if (node->index < index)
			p = &(*p)->rb_left;
		else if (node->index > index)
			p = &(*p)->rb_right;
		else
			return node;
	}

	node = kzalloc(sizeof(*node), GFP_KERNEL);
	if (!node)
		return NULL;
	node->index = index;

	rb_link_node(&node->node, parent, p);
	rb_insert_color(&node->node, &cache->root);

	return node;
}

int owner_cache_add_root(struct owner_cache *cache, u64 root)
{
	struct owner_cache_node *node;
	u64 index = OWNER_CACHE_INDEX(root);
	unsigned bit = OWNER_CACHE_BIT(root);

	node = find_or_create_cache_node(cache, index);
	if (!node)
		return -ENOMEM;

	if (!test_bit(bit, node->bitmap)) {
		set_bit(bit, node->bitmap);
		cache->refs++;
	}

	return 0;
}

void owner_cache_release(struct owner_cache *cache)
{
	struct rb_node *node;

	node = rb_first(&cache->root);
	while (node) {
		struct owner_cache_node *cnode = to_cache_node(node);
		node = rb_next(node);

		rb_erase(&cnode->node, &cache->root);
		kfree(cnode);
	}

	cache->refs = 0;
}

int owner_cache_clone(struct owner_cache *src, struct owner_cache *dst)
{
	struct rb_node *node;

	node = rb_first(&src->root);
	while (node) {
		struct owner_cache_node *cache_node = to_cache_node(node);
		struct owner_cache_node *new_cache_node;

		new_cache_node = find_or_create_cache_node(dst,
							   cache_node->index);
		if (!new_cache_node) {
			owner_cache_release(dst);
			return -ENOMEM;
		}

		memcpy(new_cache_node->bitmap, cache_node->bitmap,
		       sizeof(cache_node->bitmap));

		node = rb_next(node);
	}

	return 0;
}

int owner_cache_merge(struct owner_cache *src, struct owner_cache *dst)
{
	struct rb_node *node;
	int ret;

	node = rb_first(&src->root);
	while (node) {
		struct owner_cache_node *cache_node = to_cache_node(node);
		unsigned bit;
		u64 base;

		base = cache_node->index << OWNER_CACHE_INDEX_BITS;
		for_each_set_bit(bit, cache_node->bitmap, OWNER_CACHE_SIZE) {
			u64 root = base + bit;
			ret = owner_cache_add_root(dst, root);
			BUG_ON(ret);
			if (ret)
				return ret;
		}
		node = rb_next(node);
	}

	return 0;
}


int owner_cache_iterate_owners(struct owner_cache *cache,
			       int (*callback)(struct owner_cache *cache,
					       u64 root, void *data),
				void *data)
{
	struct rb_root *root = &cache->root;
	struct rb_node *node;
	int ret = 0;

	if (RB_EMPTY_ROOT(root))
		return ret;

	node = rb_first(root);
	while (node) {
		struct owner_cache_node *cache_node = to_cache_node(node);
		u64 base = cache_node->index << OWNER_CACHE_INDEX_BITS;
		unsigned bit;

		for_each_set_bit(bit, cache_node->bitmap, OWNER_CACHE_SIZE) {
			u64 root = base + bit;
			ret = callback(cache, root, data);
			if (ret)
				return ret;
		}

		node = rb_next(node);
	}

	return ret;
}

#if 0
static int print_owner(struct owner_cache *cache, u64 root, void *data)
{
	printk(" %llu", root);
	return 0;
}

void owner_cache_dump(struct owner_cache *cache)
{
	printk("owners:");
	owner_cache_iterate_owners(cache, print_owner, NULL);
	printk("\n");
}
#endif

void owner_cache_destroy(struct owner_cache *cache)
{
	struct rb_node *node;
	while ((node = rb_first(&cache->root))) {
		struct owner_cache_node *cache_node = to_cache_node(node);
		rb_erase(node, &cache->root);
		kfree(cache_node);
	}
}

/*
 * Performance opportunity: maintain a tree of owners and reference those.
 * We can do a pointer comparison for merging operations.
 */
bool owner_cache_compare(struct owner_cache *cache1,
			 struct owner_cache *cache2)
{
	struct rb_node *node1, *node2;

	if (RB_EMPTY_ROOT(&cache1->root)) {
		printk("cache1 is empty\n");
		return false;
	}

	if (RB_EMPTY_ROOT(&cache2->root)) {
		printk("cache2 is empty\n");
		return false;
	}

	if (cache1->refs != cache2->refs) {
		printk("different refs %llu %llu\n", cache1->refs, cache2->refs);
		return false;
	}

	node1 = rb_first(&cache1->root);
	node2 = rb_first(&cache2->root);

	while (node1 && node2) {
		struct owner_cache_node *cnode1 = to_cache_node(node1);
		struct owner_cache_node *cnode2 = to_cache_node(node2);

		if (cnode1->index != cnode2->index) {
			printk("different index %llu %llu\n", cnode1->index, cnode2->index);
			return false;
		}

		if (memcmp(cnode1->bitmap, cnode2->bitmap,
			   sizeof(cnode1->bitmap))) {
			printk("memcmp failed\n");
			return false;
		}

		node1 = rb_next(node1);
		node2 = rb_next(node2);
	}

	return true;
}
