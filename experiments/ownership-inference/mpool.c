/*
 * Copyright 2018 The Hafnium Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "hf/mpool.h"

#include <stdbool.h>

/*  
 *  Lifetime of an object managed by a mpool
 *  (1) Execuction start => span within a statically allocated as an array
 *  (2) Addition to mpool => span within a mpool chunk
 *  (3) Allocation => page table node - either a root, an internal node, or a leaf
 *  (4) Deallocation => mpool entry or mpool chunk
 */

/* 
 * How type works on global variables
 *
 * struct {
 *     const c;
 *     lock;
 *     data;
 * } g;
 *
 * a = & g; //@ a : unlocked shared reference
 * 
 * case1: a->c => GOOD
 * case2: acquire(&a->lock) => GOOD
 * case3: release(&a->lock) => BAD
 * case4: a->data => BAD
 *
 * acquire(&a->lock); //@ a : locked mutable reference
 * 
 * case1: a->c => GOOD
 * case2: acquire(&a->lock) => BAD
 * case3: release(&a->lock) => GOOD
 * case4: a->data => GOOD
 *
 * release(&a->lock); //@ a : unlocked shared reference * 	 
 */

/* 
 * struct mpool_chunk *ptr; //@ own
 * 
 * (1) The layout of OBJECT(ptr) is consistent with mpool_chunk.
 *     Assuming 64bit addressing, the first 8 bytes point to a mpool_chunk.
 *     The next 8 bytes point to the end of a mpool_chunk. It can't be NULL.
 * (2) ptr owns SPAN(ptr, ptr->limit).
 *     It means that no valid pointer in the current execution state
 *     can point to a location within SPAN(ptr, ptr->limit).
 * (3) If not NULL, ptr->next_chunk owns SPAN(ptr->next_chunk, ptr->limit).
 * (4) ptr->limit can be used only for comparision.
 *     It cannot be dereferenced to read/write content.
 */

struct mpool_chunk {
	struct mpool_chunk *next_chunk; //@ own, optional
	struct mpool_chunk *limit; //@ no_access
};

/*
 * struct mpool_entry *ptr; //@ own
 *
 * Let's assume that mpool is a pool that the entry belongs to. Then,
 * (1) The layout of OBJECT(ptr) is consistent with mpool_entry.
 *     Assuming 64bit addressing, the first 8 bytes are NULL or point to a mpool_entry.
 *     The next 8 bytes point to the end of a mpool_chunk. It can't be NULL.
 * (2) ptr owns SPAN(ptr, ptr + mpool->entry_size).
 *     It means that no valid pointer in the current execution state
 *     can point to a location within SPAN(ptr, ptr + mpool->entry_size)
 *     where mpool is a pools that the entry belongs to.
 * (3) If not NULL, ptr->next owns SPAN(ptr->next, mpool->entry_size).
 */

struct mpool_entry {
	struct mpool_entry *next; // @own
};

/*
 * TODO: How to understand global variables?
 */
 
static bool mpool_locks_enabled = false;

void mpool_enable_locks(void)
{
	mpool_locks_enabled = true;
}

static void mpool_lock(struct mpool *p)
{
	if (mpool_locks_enabled) {
		sl_lock(&p->lock);
	}
}

static void mpool_unlock(struct mpool *p)
{
	if (mpool_locks_enabled) {
		sl_unlock(&p->lock);
	}
}

/*
 * This is mpool's constructor. It should be called before doing anything on mpool.
 * 
 * Input parameters 
 *     p : must be a mutuble reference of OBJECT(p).
 */

void mpool_init(struct mpool *p, size_t entry_size)
{
	// To update OBJECT(p), p must either own or have mutuble reference to OBJECT(p).
	// Since p is an input parameter and is mutable reference, it should be fine.
	p->entry_size = entry_size;
	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;
	sl_init(&p->lock); // TODO
}

/*
 * Constructor of pool. Dependent on another constructor mpool_init(struct mpool* , t_size).
 * 
 * Input parameters
 *     p : mutable reference. The reference is destoryed when the function ends execution.
 *     from : unlocked shared reference.
 *            In addition, from points to a synchronized object, guarded by from->lock.
 *            So, to access from's data (other than its lock), from->lock must be acquired.
 */

void mpool_init_from(struct mpool *p, struct mpool *from)
{	
	mpool_init(p, from->entry_size); // TODO

    // TODO : Depending on the execution is in a single-thread vs. multi-thread mode,
	//        mpool_lock() may or may not acquire from->lock.
	mpool_lock(from); // TODO

	p->chunk_list = from->chunk_list; // Ownership is transferred.
	p->entry_list = from->entry_list; // Ownership is transferred.

    // This is mutable reference transfer.
    // It is a little bit more complicated since we need to reason about lifetime.
	// One simple solution is, we assert from->fallback is NULL.
	// Then, there is no actual mutable reference transfer so we do not need lifetime reasoning.

	p->fallback = from->fallback; // assert(from->fallback == NULL)
	 
	from->chunk_list = NULL; // Since from->chunk_list lost ownership, it should be reset to NULL.
	from->entry_list = NULL; // Since entry->chunk_list lost ownership, it should be reset to NULL.	
	from->fallback = NULL; // Redudant if from->fallback is NULL

	mpool_unlock(from); // TODO
}

/*
 * Input parameters
 *     p : mutable reference. The reference is destoryed when the function ends execution.
 *     fallback : unlocked shared reference. The reference is evetually transfered to p->fallback.
 *         To do so, the following constraint must be met.
 */

void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback)
{
	mpool_init(p, fallback->entry_size); // TODO

    // Mutable reference is transferred from fallback to p->fallback.
	// The following constraint must be met.
	//     LIFETIME(OBJECT(fallback) >= LIFETIME(OBJECT(p))

	p->fallback = fallback;
}

/*
 * Input parameters
 *     p : mutable reference. The reference is destoryed when the function ends execution.
 */

void mpool_fini(struct mpool *p)
{
	struct mpool_entry *entry;
	struct mpool_chunk *chunk;

	if (!p->fallback) {
		return;
	}

    // TODO: If we have a mutable reference to p, should we still lock/unlock p?
    mpool_lock(p);

    // Ownership is transferred from p->entry_list to entry.
	// Until updated, p->entry_list is inaccessible.
	entry = p->entry_list;

	while (entry != NULL) {
		// At this point, entry owns ObJECT(entry).
		// After executing this statement, the ownership is transferred to ptr.
		void *ptr = entry;

		// TODO: entry should be inaccessiable at this point. we need to use ptr instead.
        // entry gains an ownership of the next object.
		entry = entry->next;

        // TODO: Assure that p->fallback->entry_size is the same as size of OBJECT(ptr).
		// NOTE: It looks like per mpool entry_size is actually meaningless in the current implementation.
		// Ownership is transferred from ptr to p->fallback.
		mpool_free(p->fallback, ptr);
	}

    // Ownership is transferred from p->chunk_list to chunk.
	// Until updated, p->chunk_list is inaccessible.
	chunk = p->chunk_list;

	while (chunk != NULL) {
		// At this point, chunk owns SPAN(chunk, chunk->limit).
		void *ptr = chunk;

		// TODO: chunk is inaccessible at this point. Use ptr instead.
		size_t size = (uintptr_t)chunk->limit - (uintptr_t)chunk;

        // TODO: chunk is inaccessible at this point. Use ptr instead.
		// chunk gains an ownership of the next chunk.
		chunk = chunk->next_chunk;

		// Ownership of SPAN(ptr, ptr + size) is transferred from ptr to p->fallback.
		mpool_add_chunk(p->fallback, ptr, size);
	}

	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;

    // TODO: The same question.
	// If we have a mutable reference to p, should we still lock/unlock p?
	mpool_unlock(p);
}

bool mpool_add_chunk(struct mpool *p, void *begin, size_t size)
{
	struct mpool_chunk *chunk;
	uintptr_t new_begin;
	uintptr_t new_end;

	new_begin = (((uintptr_t)begin + p->entry_size - 1) / p->entry_size) * p->entry_size;
	new_end = (((uintptr_t)begin + size) / p->entry_size) * p->entry_size;

	if (new_begin >= new_end || new_end - new_begin < p->entry_size) {
		return false;
	}

	chunk = (struct mpool_chunk *)new_begin;
	chunk->limit = (struct mpool_chunk *)new_end;

	mpool_lock(p);
	chunk->next_chunk = p->chunk_list;
	p->chunk_list = chunk;
	mpool_unlock(p);

	return true;
}

struct Mpool {
    Lock lock;
    struct Data {
        EntryList* entry_list;
        ChunkList* chunk_list;
    } data;
};

//@ p : unlocked shared reference
static void *mpool_alloc_no_fallback(struct mpool *p)
{
	void *ret;
	struct mpool_chunk *chunk;
	struct mpool_chunk *new_chunk;

    //@ ret : optional dead
	//@ chunk : optinoal dead
	//@ new_chunk : optional dead

    // Since p is an unlocked shared reference, we can perform lock on p->lock.
	// Afer performing lock, p will turn into a mutable reference.

    // mpool_lock()
	//     precondition
	//         p : unlocked shared reference of mpool
	//     postcondition
	//         p : locked mutual reference

    //@ p : unlocked shared reference
	mpool_lock(p);
	//@ p : locked mutual reference

    // Since p is a mutuable reference, we can modify its entry list.
	// (1) If p->entry_list is NULL, there is nothing to do.
	//     We will check chunk instead.
	// (2) If p->entry_list is not NULL, we will return the first entry 
	//     while updating p->entry_list to point to the second entry.

    //@ p->entry_list : optional owner
	if (p->entry_list != NULL) {
	    // At this point, we know that p->entry_list is not NULL.
		// We can refine its type from optional owner to owner.

		// [TODO] In this code, the mpool_entry invariant of p is broken temporarily.
		// One of the key quetions is how to handle such cases.

		//@ p->entry_list : owner
		struct mpool_entry *entry = p->entry_list;
		//@ entry : owner
		//@ p->entry_list : dead

		// Ownership was transferred from p->entry_list to entry.
		// p->entry_list remains dead temporarily until it gets updated.

        //@ p->entry_list : dead
		//@ entry->next : optional owner
		p->entry_list = entry->next;
        //@ p->entry_list  : optional owner
		//@ entry->next : optional dead

		// [TODO] Ownership was transferred from entry->next to p->entry_list.
		// entry->next remain optional dead until it gets updated.
		// Effectively, the mpool_entry invariant of entry is broken temporarily.
        // We need to figure out how to handle such cases.

        //@ ret : optional dead
		//@ entry : owner
		ret = entry;
		//@ ret : owner
		//@ entry : dead

		// [TODO] Note that entry violates the mpool_entry invariant since entry->next is optional dead at this point.
	    // However, since entry's life is about to end, we don't need to fix it.
        // We need to figure out how to handling this reasoning.

		// The ownership of the object pointed to by ret is evetually transferred to the caller. 
		// To do so, ret should own the object at this point.

		goto exit;
	}

	//@ chunk : optional dead
    //@ p->chunk_list : optional owner
	chunk = p->chunk_list;	
	//@ chunk : optional owner
	//@ p->chunk_list : optional dead

    //@ chunk : optional owner
	if (chunk == NULL) {
		//@ chunk : NULL
		ret = NULL;
		//@ ret : NULL
		goto exit;
	}
    //@ chunk : owner
	//@ p->chunk_list : dead

	// Type invariant of chunk assures that if chunk is an owner,
	// it owns a span from chunk to chunk->limit.
    // This is an ownership split point.

    // [TODO] The invariant around chunk->limit is temporarily broken.
	// Are we O.K. with it as long as it gets recovered pretty soon so that it won't impact anything.
	// Before we exit this function, we will destory "struct mpool_chunk" at (chunk, chunk->limit).
	// Therefore, the broken invariant does not affect anything, right?
    // [TODO] What if we read chunk->next_chunk and chunk->limit into variables as follows?
	//     next_chunk = chunk->next_chunk;
	//     chunk_limit = chunk->limit;
	// Then, we don't need to read any field from a broken chunk?

    //@ chunk : owner
    //@ chunk : owner(chunk, chunk->limit)
	//@ new_chunk : optional dead
 	new_chunk = (struct mpool_chunk *)((uintptr_t)chunk + p->entry_size);
    //@ chunk : own(chunk, chunk + entry_size)
	//@ create(struct page, (chunk, chunk + entry_size))
	//@ destroy(struct chunk, (chunk, chunk->limit))

    // [TODO] shouldn't this be "==" instead of ">="?

	if (new_chunk >= chunk->limit) {
		//@ new_chunk : dead
	    // p->chunk_list : dead
		// chunk : owner
		// chunk->next_chunk : optional owner
		p->chunk_list = chunk->next_chunk;
        // p->chunk_list : optional owner
		// chunk : owner
		// chunk->next_chunk : optional dead
	} else {
		//@ new_chunk : own(chunk + entry_size, chunk->limit) if chunk+entry_size < chunk->limit
		//@ create(struct mpool_chunk, (chunk + entry_size, chunk->limit)) if chunk+entry_size < chunk->limit

		// We know that because new and new_chunk eventuall transfer their ownership to other locations.
    	// This is also a point at which a new entry and chunk get created.
		// Effectively, the old chunk gets destructed.

		// [TODO] We may want to use the following instead:
		//     new_chunk->next_chunk = next_chunk;
		//     new_chunk->limit = chunk_limit;
		*new_chunk = *chunk;
		// [TODO] Now, OBJECT(new_chunk) has been properly initialized.
		// The chunk type's invariants would hold from now on.

		p->chunk_list = new_chunk;
		//@ p->chunk_list : owner
		//@ new_chunk : dead
	}

	//@ chunk : type(page), owner
	ret = chunk;
	//@ chunk : dead
	//@ ret : owner
exit:
	//@ p : locked mutable reference
	mpool_unlock(p);
	//@ p : unlocked shared reference

	//@ ret : optional owner
	return ret;
}

void *mpool_alloc(struct mpool *p)
{
	do {
		void *ret = mpool_alloc_no_fallback(p);

		if (ret != NULL) {
			return ret;
		}

		p = p->fallback;
	} while (p != NULL);

	return NULL;
}

void mpool_free(struct mpool *p, void *ptr)
{
	struct mpool_entry *e = ptr;

	mpool_lock(p);
	e->next = p->entry_list;
	p->entry_list = e;
	mpool_unlock(p);
}

void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count,
					 size_t align)
{
	struct mpool_chunk **prev;
	void *ret = NULL;

	align *= p->entry_size;

	mpool_lock(p);

	prev = &p->chunk_list;
	while (*prev != NULL) {
		uintptr_t start;
		struct mpool_chunk *new_chunk;
		struct mpool_chunk *chunk = *prev;

		start = (((uintptr_t)chunk + align - 1) / align) * align;

		new_chunk =
			(struct mpool_chunk *)(start + (count * p->entry_size));
		if (new_chunk <= chunk->limit) {
			/* Remove the consumed area. */
			if (new_chunk == chunk->limit) {
				*prev = chunk->next_chunk;
			} else {
				*new_chunk = *chunk;
				*prev = new_chunk;
			}

			if (start - (uintptr_t)chunk >= p->entry_size) {
				chunk->next_chunk = *prev;
				*prev = chunk;
				chunk->limit = (struct mpool_chunk *)start;
			}

			ret = (void *)start;
			break;
		}

		prev = &chunk->next_chunk;
	}

	mpool_unlock(p);

	return ret;
}

void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align)
{
	do {
		void *ret = mpool_alloc_contiguous_no_fallback(p, count, align);

		if (ret != NULL) {
			return ret;
		}

		p = p->fallback;
	} while (p != NULL);

	return NULL;
}
