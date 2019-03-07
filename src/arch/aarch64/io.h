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

#include <stddef.h>
#include <stdint.h>

#include "hf/arch/barriers.h"

static inline uint32_t io_read(uintptr_t addr)
{
	return *(volatile uint32_t *)addr;
}

static inline uint32_t io_read_mb(uintptr_t addr)
{
	uint32_t v = io_read(addr);

	dsb();
	isb();

	return v;
}

static inline void io_write(uintptr_t addr, uint32_t v)
{
	*(volatile uint32_t *)addr = v;
}

static inline void io_write_mb(uintptr_t addr, uint32_t v)
{
	dsb();
	isb();
	io_write(addr, v);
}
