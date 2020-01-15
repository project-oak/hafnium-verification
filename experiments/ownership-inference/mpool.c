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

/* HSK
 * Represents an unallocated memory segment of a variabe size
 * that begins from this and then ends at this->limit
 * At the beginning, the pointer to the next chunk within the same mpool is stored.
 * If this is the last chunk in the mpoool, *this is NULL.
 */

struct mpool_chunk {
	struct mpool_chunk *next_chunk;
	struct mpool_chunk *limit;
};

/* HSK
 * Represents an unallocated memory segment of a page size.
 * The first 64 bit points to the next entry in the same mpool.
 * If it is the last entry, the pointer is NULL.
 */

struct mpool_entry {
	struct mpool_entry *next;
};

/** [HSK]
 * Global variables are just variables at the top of the stack and never get popped out.
 * Immutable field of a global variable can be read at any time.
 * However, since any thread can access them, its mutable field should be projected by locks.
 * So, a global variable itself only has "lock acquiring" permission to its mutable fields.
 * It is granted read/write permission only when it acquires a lock.
 * When the lock is released, its permission is lost.
 */
 
static bool mpool_locks_enabled = false;

/**
 * Enables the locks protecting memory pools. Before this function is called,
 * the locks are disabled, that is, acquiring/releasing them is a no-op.
 */
void mpool_enable_locks(void)
{
	mpool_locks_enabled = true;
}

/**
 * Acquires the lock protecting the given memory pool, if locks are enabled.
 */
static void mpool_lock(struct mpool *p)
{
	if (mpool_locks_enabled) {
		sl_lock(&p->lock);
	}
}

/**
 * Releases the lock protecting the given memory pool, if locks are enabled.
 */
static void mpool_unlock(struct mpool *p)
{
	if (mpool_locks_enabled) {
		sl_unlock(&p->lock);
	}
}

/**
 * Initialises the given memory pool with the given entry size, which must be
 * at least the size of two pointers.
 *
 * All entries stored in the memory pool will be aligned to at least the entry
 * size.
 */
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

/**
 * Initialises the given memory pool by replicating the properties of `from`. It
 * also pulls the chunk and free lists from `from`, consuming all its resources
 * and making them available via the new memory pool.
 */

/**
 * [HSK] This is an interesting point.
 * The ownership of some objects reachable from "from" is transferred to "p".
 * It means that from must own them. The only way to own them is to own object(from).
 *
 * fallback is an interesting field.
 * Since mpool has its own lock, exclusivity is guaranteed by acquiring the lock.
 * So, what we distribute is the ownership to acquire lock. 
 * Once the lock is acquired, then we grant the ownership to read/write mutable fields.
 *
 * Another intersting point:
 * When mpool_init and its variants are called, either execution is in a single-thread mode
 * or p has not escaped the thread, yet. Hmmm. We also need thread escape analysis!
 * Or, p->lock must have been acquired. But, I am not sure if that's what we need.
 */

void mpool_init_from(struct mpool *p, struct mpool *from)
{
	mpool_init(p, from->entry_size);

	mpool_lock(from);
	p->chunk_list = from->chunk_list;
	p->entry_list = from->entry_list;
	p->fallback = from->fallback;

        // [HSK] This is an interesting point.
        // Since from->chunk_list lost ownership, it should be reset.
        // or acquire the ownership of a different object. 
        // The same for other fields that require exclusive ownership.

	from->chunk_list = NULL;
	from->entry_list = NULL;
	from->fallback = NULL;
	mpool_unlock(from);
}

/**
 * Initialises the given memory pool with a fallback memory pool if this pool
 * runs out of memory.
 */

// [HSK] This is another interesting point.
// From the escape analysis' perspective, object(fallback) escapes to p->fallback.
// Therefore, ownership should be transferred.
// However, object(p) is always a local mpool thus temporary.
//
// Another interesting point is that fallback is supposed to have multiple
// references spread across threads. For actual reference, it needs to 
// acquire the lock embedded in the object to access mutable fields.
// Access to immutable fields should be fine.

// [HSK] So, at this within this thread - we should guarantee that p->fallback is
// is the only mutable reference. In the current implementation, it appears pretty straightforward.

void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback)
{
	mpool_init(p, fallback->entry_size);
	p->fallback = fallback;
}

/**
 * Finishes the given memory pool, giving all free memory to the fallback pool
 * if there is one.
 */

void mpool_fini(struct mpool *p)
{
	struct mpool_entry *entry;
	struct mpool_chunk *chunk;

        // [HSK] This is interesting.
        // Are we safe to do this without lock?
        // Probably, assuming that mpool_init variant was properly called,
        // they are called only once? If mpool_fini is called multiple times,
        // nothing will happen in the second call?

	if (!p->fallback) {
		return;
	}

	mpool_lock(p);

	/* Merge the freelist into the fallback. */
	entry = p->entry_list;
	while (entry != NULL) {
		void *ptr = entry;

		entry = entry->next;

                // [HSK] I think this is safe.
                // However, it is pretty tricky to reason about it
                // since if mpool_fini is concurrently called,
                // in one of the calls, p->fallback could be NULL at this point.
                // Well, however, when that happens, p->entry_list should be NULL, too.
                // So, we wouldn't get to this point in the first place.
                // 
                // What do we want to do about it? Are we O.K. with it?
                 
		mpool_free(p->fallback, ptr);
	}

	/* Merge the chunk list into the fallback. */
	chunk = p->chunk_list;
	while (chunk != NULL) {
		void *ptr = chunk;
		size_t size = (uintptr_t)chunk->limit - (uintptr_t)chunk;

		chunk = chunk->next_chunk;
		mpool_add_chunk(p->fallback, ptr, size);
	}

	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;

	mpool_unlock(p);
}

/**
 * Adds a contiguous chunk of memory to the given memory pool. The chunk will
 * eventually be broken up into entries of the size held by the memory pool.
 *
 * Only the portions aligned to the entry size will be added to the pool.
 *
 * Returns true if at least a portion of the chunk was added to pool, or false
 * if none of the buffer was usable in the pool.
 */

/* [HSK]
   p must be a valid mpool.
   The memory segment represented by "begin" should have length >= size.
   And, begin should own the memory segment. No one else has a live pointer to any part of it.

   begin must exclusively own the referenced object.
   It is because the object is eventually stored into an object referenced by p.
   This is very similar to the concept of "escape".
*/

bool mpool_add_chunk(struct mpool *p, void *begin, size_t size)
{
	struct mpool_chunk *chunk;
	uintptr_t new_begin;
	uintptr_t new_end;

	/* Round begin address up, and end address down. */
        /* [HSK] p->entry_size should be immutable at this point */

	new_begin = ((uintptr_t)begin + p->entry_size - 1) / p->entry_size *
		    p->entry_size;
	new_end = ((uintptr_t)begin + size) / p->entry_size * p->entry_size;

	/* Nothing to do if there isn't enough room for an entry. */
	if (new_begin >= new_end || new_end - new_begin < p->entry_size) {
		return false;
	}

	chunk = (struct mpool_chunk *)new_begin;
	chunk->limit = (struct mpool_chunk *)new_end;

	mpool_lock(p);
	chunk->next_chunk = p->chunk_list;
        // [HSK] this point, the object referenced by chunk escapes
        // and should be owned by the object referenced by p.
        // Therefore, chunk must be the owner of the referenced object.
        // If you go backward from here, it implies that the input parameter begin
        // should be the owner of the referenced object.
	p->chunk_list = chunk;
	mpool_unlock(p);

	return true;
}

/**
 * Allocates an entry from the given memory pool, if one is available. The
 * fallback will not be used even if there is one.
 */

/** HSK
 * At the beginning of the fuction call, 
 * p has an ownership for all memory segments reachable from p->entry_list and p->chunk_list.
 * At the end, p still has an ownership for all memory segments reachable from p->entry_list and p->chunk_list.
 * The return variable owns the memory segment it owns. It used to belong to p but the ownership is transfered. 
 */

//@ lock projects data
struct Mpool {
    Lock lock;
    struct Data {
        EntryList* entry_list;
        ChunkList* chunk_list;
    } data;
};

struct Mpool mpool;

mpool =  new Mpool(); //@ mpool : Mpool
lock = new Lock();   //@ lock projects mpool

acquire(lock);       //@ acquire lock
                     //@ acquire lock -> mpool : &mut Mpool
page = mpool->alloc();
release(lock);       //@

//@ if type(mpool) = PTR Mpool projtecteby lock, then is_owned() == true 

//@ *
//@ own(mpool)
page = mpool->alloc();
//@ own(mpool)
//@ *

mpool->chunk_list = ....;




p


static void *mpool_alloc_no_fallback(struct mpool *p)
{
	void *ret;
	struct mpool_chunk *chunk;
	struct mpool_chunk *new_chunk;

	/* Fetch an entry from the free list if one is available. */
	mpool_lock(p);
	if (p->entry_list != NULL) {
                /* [HSK] Ownership of object(p->entry_list) is transfered to entry.
		struct mpool_entry *entry = p->entry_list;

                /* [HSK] Ownership of object(entry->next) is transferred to p->entry_list.
		p->entry_list = entry->next;
                /* [HSK] Ownership of object(entry) is transferred to ret.
		ret = entry;
		goto exit;
	}

	/* There was no free list available. Try a chunk instead. */
        // [HSK] The ownership is transferred from p->chunk_list to chunk
        // if p->chunk_list is not NULL.
	chunk = p->chunk_list;
	if (chunk == NULL) {
		/* The chunk list is also empty, we're out of entries. */
		ret = NULL;
		goto exit;
	}
        // At this point, chunk shouldn't be NULL.
        // [HSK] chunk should be the owner of the referenced object.

        // [HSK] This is a ownership split point
        // because both new_chunk and chunk eventually escape
        // thus should transfer their ownerships to other locations.
        // After this statement, chunk owns [chunk, chunk + p->entry_size)
        // while new_chunk owns [chunk + p->entry_size, chunk->limit].
	new_chunk = (struct mpool_chunk *)((uintptr_t)chunk + p->entry_size);
	if (new_chunk >= chunk->limit) {
		p->chunk_list = chunk->next_chunk;
	} else {
                // [HSK] This is a ownership transfer point.
                // object(chunk->next_chunk) is transferred to new_chunk->next_chunk.
                // One question: how should we handle "limit"?
                // This field should be used only for address comparison.
                // In that sense, it is a reference with no read/write capability.
		*new_chunk = *chunk;
		p->chunk_list = new_chunk;
	}

	ret = chunk;

exit:
	mpool_unlock(p);

        // [HSK] This is an escape point.
        // Whatever is returned here, should be owned by ret.
	return ret;
}

/**
 * Allocates an entry from the given memory pool, if one is available. If there
 * isn't one available, try and allocate from the fallback if there is one.
 */
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

/**
 * Frees an entry back into the memory pool, making it available for reuse.
 *
 * This is meant to be used for freeing single entries. To free multiple
 * entries, one must call mpool_add_chunk instead.
 */
void mpool_free(struct mpool *p, void *ptr)
{
	struct mpool_entry *e = ptr;

	/* Store the newly freed entry in the front of the free list. */
	mpool_lock(p);
	e->next = p->entry_list;
	p->entry_list = e;
	mpool_unlock(p);
}

/**
 * Allocates a number of contiguous and aligned entries. If a suitable
 * allocation could not be found, the fallback will not be used even if there is
 * one.
 */
void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count,
					 size_t align)
{
	struct mpool_chunk **prev;
	void *ret = NULL;

	align *= p->entry_size;

	mpool_lock(p);

	/*
	 * Go through the chunk list in search of one with enough room for the
	 * requested allocation
	 */
	prev = &p->chunk_list;
	while (*prev != NULL) {
		uintptr_t start;
		struct mpool_chunk *new_chunk;
		struct mpool_chunk *chunk = *prev;

		/* Round start address up to the required alignment. */
		start = (((uintptr_t)chunk + align - 1) / align) * align;

		/*
		 * Calculate where the new chunk would be if we consume the
		 * requested number of entries. Then check if this chunk is big
		 * enough to satisfy the request.
		 */
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

			/*
			 * Add back the space consumed by the alignment
			 * requirement, if it's big enough to fit an entry.
			 */
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

/**
 * Allocates a number of contiguous and aligned entries. This is a best-effort
 * operation and only succeeds if such entries can be found in the chunks list
 * or the chunks of the fallbacks (i.e., the entry list is never used to satisfy
 * these allocations).
 *
 * The alignment is specified as the number of entries, that is, if `align` is
 * 4, the alignment in bytes will be 4 * entry_size.
 *
 * The caller can enventually free the returned entries by calling
 * mpool_add_chunk.
 */
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
