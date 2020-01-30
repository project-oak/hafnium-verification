/*
 * Copyright 2019 The Hafnium Authors.
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

#include <stdatomic.h>

/** Platform-agnostic API */

/**
 * Ensures all explicit memory accesses before this point are completed before
 * any later memory accesses are performed.
 */
#define memory_ordering_barrier() atomic_thread_fence(memory_order_seq_cst)

/**
 * Ensures all explicit memory access and management instructions have completed
 * before continuing.
 *
 * FIXME: this is just a memory barrier but, without MMIO or registers to modify
 * operation in the fake architecture, this is likely enough. If there's a way
 * to have a true synchronization then we should update it.
 */
#define data_sync_barrier() atomic_thread_fence(memory_order_seq_cst)
