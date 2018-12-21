/*
 * Copyright 2018 Google LLC
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

#include <stdalign.h>

#include <gmock/gmock.h>

extern "C" {
#include "hf/mpool.h"
}

namespace
{
using ::testing::IsNull;
using ::testing::NotNull;

/**
 * Checks that the given allocations come from the given chunks.
 */
bool check_allocs(std::vector<std::unique_ptr<char[]>>& chunks,
		  std::vector<uintptr_t>& allocs, size_t entries_per_chunk,
		  size_t entry_size)
{
	size_t i, j;

	if (allocs.size() != chunks.size() * entries_per_chunk) {
		return false;
	}

	sort(allocs.begin(), allocs.end());
	sort(chunks.begin(), chunks.end(),
	     [](const std::unique_ptr<char[]>& a,
		const std::unique_ptr<char[]>& b) {
		     return a.get() < b.get();
	     });

	for (i = 0; i < chunks.size(); i++) {
		if ((uintptr_t)chunks[i].get() !=
		    allocs[i * entries_per_chunk]) {
			return false;
		}

		for (j = 1; j < entries_per_chunk; j++) {
			size_t k = i * entries_per_chunk + j;
			if (allocs[k] != allocs[k - 1] + entry_size) {
				return false;
			}
		}
	}

	return true;
}

/**
 * Add chunks to the given mem pool and chunk vector.
 */
static void add_chunks(std::vector<std::unique_ptr<char[]>>& chunks,
		       struct mpool* p, size_t count, size_t size)
{
	size_t i;

	for (i = 0; i < count; i++) {
		chunks.emplace_back(std::make_unique<char[]>(size));
		mpool_add_chunk(p, chunks.back().get(), size);
	}
}

/**
 * Validates allocations from a memory pool.
 */
TEST(mpool, allocation)
{
	struct mpool p;
	constexpr size_t entry_size = 16;
	constexpr size_t entries_per_chunk = 10;
	constexpr size_t chunk_count = 10;
	std::vector<std::unique_ptr<char[]>> chunks;
	std::vector<uintptr_t> allocs;
	void* ret;

	mpool_init(&p, entry_size);

	/* Allocate from an empty pool. */
	EXPECT_THAT(mpool_alloc(&p), IsNull());

	/*
	 * Add a chunk that is too small, it should be ignored, and allocation
	 * should return NULL.
	 */
	mpool_add_chunk(&p, NULL, entry_size - 1);
	EXPECT_THAT(mpool_alloc(&p), IsNull());

	/* Allocate a number of chunks and add them to the pool. */
	add_chunks(chunks, &p, chunk_count, entries_per_chunk * entry_size);

	/* Allocate from the pool until we run out of memory. */
	while ((ret = mpool_alloc(&p))) {
		allocs.push_back((uintptr_t)ret);
	}

	/* Check that returned entries are within chunks that were added. */
	ASSERT_THAT(check_allocs(chunks, allocs, entries_per_chunk, entry_size),
		    true);
}

/**
 * Validates frees into a memory pool.
 */
TEST(mpool, freeing)
{
	struct mpool p;
	constexpr size_t entry_size = 16;
	constexpr size_t entries_per_chunk = 10;
	constexpr size_t chunk_count = 10;
	std::vector<std::unique_ptr<char[]>> chunks;
	std::vector<uintptr_t> allocs;
	size_t i;
	alignas(entry_size) char entry[entry_size];
	void* ret;

	mpool_init(&p, entry_size);

	/* Allocate from an empty pool. */
	EXPECT_THAT(mpool_alloc(&p), IsNull());

	/* Free an entry into the pool, then allocate it back. */
	mpool_free(&p, &entry[0]);
	EXPECT_THAT(mpool_alloc(&p), (void*)&entry[0]);
	EXPECT_THAT(mpool_alloc(&p), IsNull());

	/* Allocate a number of chunks and add them to the pool. */
	add_chunks(chunks, &p, chunk_count, entries_per_chunk * entry_size);

	/*
	 * Free again into the pool. Ensure that we get entry back on next
	 * allocation instead of something from the chunks.
	 */
	mpool_free(&p, &entry[0]);
	EXPECT_THAT(mpool_alloc(&p), (void*)&entry[0]);

	/* Allocate from the pool until we run out of memory. */
	while ((ret = mpool_alloc(&p))) {
		allocs.push_back((uintptr_t)ret);
	}

	/*
	 * Free again into the pool. Ensure that we get entry back on next
	 * allocation instead of something from the chunks.
	 */
	mpool_free(&p, &entry[0]);
	EXPECT_THAT(mpool_alloc(&p), (void*)&entry[0]);

	/* Add entries back to the pool by freeing them. */
	for (i = 0; i < allocs.size(); i++) {
		mpool_free(&p, (void*)allocs[i]);
	}
	allocs.clear();

	/* Allocate from the pool until we run out of memory. */
	while ((ret = mpool_alloc(&p))) {
		allocs.push_back((uintptr_t)ret);
	}

	/* Check that returned entries are within chunks that were added. */
	ASSERT_THAT(check_allocs(chunks, allocs, entries_per_chunk, entry_size),
		    true);
}

/**
 * Initialises a memory pool from an existing one.
 */
TEST(mpool, init_from)
{
	struct mpool p, q;
	constexpr size_t entry_size = 16;
	constexpr size_t entries_per_chunk = 10;
	constexpr size_t chunk_count = 10;
	std::vector<std::unique_ptr<char[]>> chunks;
	std::vector<uintptr_t> allocs;
	size_t i;
	void* ret;

	mpool_init(&p, entry_size);

	/* Allocate a number of chunks and add them to the pool. */
	add_chunks(chunks, &p, chunk_count, entries_per_chunk * entry_size);

	/* Allocate half of the elements. */
	for (i = 0; i < entries_per_chunk * chunk_count / 2; i++) {
		void* ret = mpool_alloc(&p);
		ASSERT_THAT(ret, NotNull());
		allocs.push_back((uintptr_t)ret);
	}

	/* Add entries back to the pool by freeing them. */
	for (i = 0; i < allocs.size(); i++) {
		mpool_free(&p, (void*)allocs[i]);
	}
	allocs.clear();

	/* Initialise q from p. */
	mpool_init_from(&q, &p);

	/* Allocation from p must now fail. */
	EXPECT_THAT(mpool_alloc(&p), IsNull());

	/* Allocate from q until we run out of memory. */
	while ((ret = mpool_alloc(&q))) {
		allocs.push_back((uintptr_t)ret);
	}

	/* Check that returned entries are within chunks that were added. */
	ASSERT_THAT(check_allocs(chunks, allocs, entries_per_chunk, entry_size),
		    true);
}

/**
 * Initialises a memory pool from an existing one.
 */
TEST(mpool, alloc_contiguous)
{
	struct mpool p;
	constexpr size_t entry_size = 16;
	constexpr size_t entries_per_chunk = 12;
	constexpr size_t chunk_count = 10;
	std::vector<std::unique_ptr<char[]>> chunks;
	std::vector<uintptr_t> allocs;
	size_t i;
	void* ret;
	uintptr_t next;

	mpool_init(&p, entry_size);

	/* Allocate a number of chunks and add them to the pool. */
	add_chunks(chunks, &p, chunk_count, entries_per_chunk * entry_size);

	/*
	 * Allocate entries until the remaining chunk is aligned to 2 entries,
	 * but not aligned to 4 entries.
	 */
	do {
		ret = mpool_alloc(&p);
		ASSERT_THAT(ret, NotNull());
		allocs.push_back((uintptr_t)ret);
		next = (uintptr_t)ret / entry_size + 1;
	} while ((next % 4) != 2);

	/* Allocate 5 entries with an alignment of 4. So two must be skipped. */
	ret = mpool_alloc_contiguous(&p, 5, 4);
	ASSERT_THAT(ret, NotNull());
	ASSERT_THAT((uintptr_t)ret, (next + 2) * entry_size);
	for (i = 0; i < 5; i++) {
		allocs.push_back((uintptr_t)ret + i * entry_size);
	}

	/* Allocate a whole chunk. */
	ret = mpool_alloc_contiguous(&p, entries_per_chunk, 1);
	ASSERT_THAT(ret, NotNull());
	for (i = 0; i < entries_per_chunk; i++) {
		allocs.push_back((uintptr_t)ret + i * entry_size);
	}

	/* Allocate 2 entries that are already aligned. */
	ret = mpool_alloc_contiguous(&p, 2, 1);
	ASSERT_THAT(ret, NotNull());
	allocs.push_back((uintptr_t)ret);
	allocs.push_back((uintptr_t)ret + entry_size);

	/* Allocate from p until we run out of memory. */
	while ((ret = mpool_alloc(&p))) {
		allocs.push_back((uintptr_t)ret);
	}

	/* Check that returned entries are within chunks that were added. */
	ASSERT_THAT(check_allocs(chunks, allocs, entries_per_chunk, entry_size),
		    true);
}

} /* namespace */
