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

#pragma once

#include <stdbool.h>
#include <stddef.h>

#include "hf/spinlock.h"

struct mpool {
	struct spinlock lock;
	struct mpool_chunk *chunk_list;
	struct mpool_entry *entry_list;
	struct mpool *fallback;
};

void mpool_enable_locks(void);
void mpool_init(struct mpool *p, size_t entry_size);
void mpool_init_from(struct mpool *p, struct mpool *from);
void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback);
void mpool_fini(struct mpool *p);
bool mpool_add_chunk(struct mpool *p, void *begin, size_t size);
void *mpool_alloc(struct mpool *p);
void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align);
void mpool_free(struct mpool *p, void *ptr);
