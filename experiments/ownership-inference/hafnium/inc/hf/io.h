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

#include <stddef.h>
#include <stdint.h>

#include "hf/arch/barriers.h"

#include "hf/check.h"

/* Opaque types for different sized fields of memory mapped IO. */

typedef struct {
	volatile uint8_t *ptr;
} io8_t;

typedef struct {
	volatile uint16_t *ptr;
} io16_t;

typedef struct {
	volatile uint32_t *ptr;
} io32_t;

typedef struct {
	volatile uint64_t *ptr;
} io64_t;

typedef struct {
	volatile uint8_t *base;
	size_t count;
} io8_array_t;

typedef struct {
	volatile uint16_t *base;
	size_t count;
} io16_array_t;

typedef struct {
	volatile uint32_t *base;
	size_t count;
} io32_array_t;

typedef struct {
	volatile uint64_t *base;
	size_t count;
} io64_array_t;

/* Contructors for literals. */

#define IO8_C(addr) ((io8_t){.ptr = (volatile uint8_t *)(addr)})
#define IO16_C(addr) ((io16_t){.ptr = (volatile uint16_t *)(addr)})
#define IO32_C(addr) ((io32_t){.ptr = (volatile uint32_t *)(addr)})
#define IO64_C(addr) ((io64_t){.ptr = (volatile uint64_t *)(addr)})

#define IO8_ARRAY_C(addr, cnt) \
	((io8_array_t){.base = (volatile uint8_t *)(addr), .count = (cnt)})
#define IO16_ARRAY_C(addr, cnt) \
	((io16_array_t){.base = (volatile uint16_t *)(addr), .count = (cnt)})
#define IO32_ARRAY_C(addr, cnt) \
	((io32_array_t){.base = (volatile uint32_t *)(addr), .count = (cnt)})
#define IO64_ARRAY_C(addr, cnt) \
	((io64_array_t){.base = (volatile uint64_t *)(addr), .count = (cnt)})

/** Read from memory-mapped IO. */

static inline uint8_t io_read8(io8_t io)
{
	return *io.ptr;
}

static inline uint16_t io_read16(io16_t io)
{
	return *io.ptr;
}

static inline uint32_t io_read32(io32_t io)
{
	return *io.ptr;
}

static inline uint64_t io_read64(io64_t io)
{
	return *io.ptr;
}

static inline uint8_t io_read8_array(io8_array_t io, size_t n)
{
	CHECK(n < io.count);
	return io.base[n];
}

static inline uint16_t io_read16_array(io16_array_t io, size_t n)
{
	CHECK(n < io.count);
	return io.base[n];
}

static inline uint32_t io_read32_array(io32_array_t io, size_t n)
{
	CHECK(n < io.count);
	return io.base[n];
}

static inline uint64_t io_read64_array(io64_array_t io, size_t n)
{
	CHECK(n < io.count);
	return io.base[n];
}

/**
 * Read from memory-mapped IO with memory barrier.
 *
 * The read is ordered before subsequent memory accesses.
 */

static inline uint8_t io_read8_mb(io8_t io)
{
	uint8_t v = io_read8(io);

	data_sync_barrier();
	return v;
}

static inline uint16_t io_read16_mb(io16_t io)
{
	uint16_t v = io_read16(io);

	data_sync_barrier();
	return v;
}

static inline uint32_t io_read32_mb(io32_t io)
{
	uint32_t v = io_read32(io);

	data_sync_barrier();
	return v;
}

static inline uint64_t io_read64_mb(io64_t io)
{
	uint64_t v = io_read64(io);

	data_sync_barrier();
	return v;
}

static inline uint8_t io_read8_array_mb(io8_array_t io, size_t n)
{
	uint8_t v = io_read8_array(io, n);

	data_sync_barrier();
	return v;
}

static inline uint16_t io_read16_array_mb(io16_array_t io, size_t n)
{
	uint16_t v = io_read16_array(io, n);

	data_sync_barrier();
	return v;
}

static inline uint32_t io_read32_array_mb(io32_array_t io, size_t n)
{
	uint32_t v = io_read32_array(io, n);

	data_sync_barrier();
	return v;
}

static inline uint64_t io_read64_array_mb(io64_array_t io, size_t n)
{
	uint64_t v = io_read64_array(io, n);

	data_sync_barrier();
	return v;
}

/* Write to memory-mapped IO. */

static inline void io_write8(io8_t io, uint8_t v)
{
	*io.ptr = v;
}

static inline void io_write16(io16_t io, uint16_t v)
{
	*io.ptr = v;
}

static inline void io_write32(io32_t io, uint32_t v)
{
	*io.ptr = v;
}

static inline void io_write64(io64_t io, uint64_t v)
{
	*io.ptr = v;
}

static inline void io_write8_array(io8_array_t io, size_t n, uint8_t v)
{
	CHECK(n < io.count);
	io.base[n] = v;
}

static inline void io_write16_array(io16_array_t io, size_t n, uint16_t v)
{
	CHECK(n < io.count);
	io.base[n] = v;
}

static inline void io_write32_array(io32_array_t io, size_t n, uint32_t v)
{
	CHECK(n < io.count);
	io.base[n] = v;
}

static inline void io_write64_array(io64_array_t io, size_t n, uint64_t v)
{
	CHECK(n < io.count);
	io.base[n] = v;
}

/*
 * Write to memory-mapped IO with memory barrier.
 *
 * The write is ordered after previous memory accesses.
 */

static inline void io_write8_mb(io8_t io, uint8_t v)
{
	data_sync_barrier();
	io_write8(io, v);
}

static inline void io_write16_mb(io16_t io, uint16_t v)
{
	data_sync_barrier();
	io_write16(io, v);
}

static inline void io_write32_mb(io32_t io, uint32_t v)
{
	data_sync_barrier();
	io_write32(io, v);
}

static inline void io_write64_mb(io64_t io, uint64_t v)
{
	data_sync_barrier();
	io_write64(io, v);
}

static inline void io_write8_array_mb(io8_array_t io, size_t n, uint8_t v)
{
	data_sync_barrier();
	io_write8_array(io, n, v);
}

static inline void io_write16_array_mb(io16_array_t io, size_t n, uint16_t v)
{
	data_sync_barrier();
	io_write16_array(io, n, v);
}

static inline void io_write32_array_mb(io32_array_t io, size_t n, uint32_t v)
{
	data_sync_barrier();
	io_write32_array(io, n, v);
}

static inline void io_write64_array_mb(io64_array_t io, size_t n, uint64_t v)
{
	data_sync_barrier();
	io_write64_array(io, n, v);
}
