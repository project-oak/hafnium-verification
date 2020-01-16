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
 *  Let ptr be a variable assigned the type PTR(mpool_chunk) as follows.
 *      struct mpool_chunk *ptr;
 * 
 *  Then,
 *  (1) ptr owns a span (ptr, limit).
 *      It means that no valid pointer in the current global state
 *      points to a location within (ptr, limit).
 *  (2) ptr->next_chunk owns OBJECT(ptr->next_chunk).
 *      This object, in in the current state, has type mpool_chunk.
 *  (3) ptr->limit can be used only for comparision.
 *      It cannot be dereferenced to read/write content.
 */

struct mpool_chunk {
	struct mpool_chunk *next_chunk; //@ own
	struct mpool_chunk *limit; //@ no_access
};

/*
 * Let ptr be a variable assigned the type PTR(mpool_entry) as follows.
 *     struct mpool_entry *ptr;
 * 
 * Then,
 *     ptr owns a span (ptr, MPOOL(ptr).entry_size).
 *     ptr->next owns OBJECT(ptr->next).
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

void mpool_init(struct mpool *p, size_t entry_size)
{
	p->entry_size = entry_size;
	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;
	sl_init(&p->lock);

    // Functional model
	p->entry_size = entry_size;
	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;
    p->lock = Lock::new();
}

/*
 * Input parameters
 *     p : mutable reference. The reference is destoryed when the function ends execution.
 *     from : mutable reference. The reference is destoryed when the function ends execution.
 */

void mpool_init_from(struct mpool *p, struct mpool *from)
{	
	mpool_init(p, from->entry_size); // TODO
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
 *     fallback : mutable reference. The reference is evetually transfered to p->fallback.
 *         To do so, the following constraint must be met.
 *             LIFETIME(OBJECT(fallback)) >= LIFTIME(OBJECT(p))
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

static void *mpool_alloc_no_fallback(struct mpool *p)
{
	void *ret;
	struct mpool_chunk *chunk;
	struct mpool_chunk *new_chunk;

	mpool_lock(p);
	if (p->entry_list != NULL) {
		struct mpool_entry *entry = p->entry_list;
		p->entry_list = entry->next;
		ret = entry;
		goto exit;
	}

	chunk = p->chunk_list;
	if (chunk == NULL) {
		ret = NULL;
		goto exit;
	}

	new_chunk = (struct mpool_chunk *)((uintptr_t)chunk + p->entry_size);
	if (new_chunk >= chunk->limit) {
		p->chunk_list = chunk->next_chunk;
	} else {
		*new_chunk = *chunk;
		p->chunk_list = new_chunk;
	}

	ret = chunk;

exit:
	mpool_unlock(p);
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
