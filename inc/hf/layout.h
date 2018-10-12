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

#pragma once

#include "hf/addr.h"

/**
 * Get the address the .text section begins at.
 */
static inline paddr_t layout_text_begin(void)
{
	extern uint8_t text_begin[];
	return pa_init((uintpaddr_t)text_begin);
}

/**
 * Get the address the .text section ends at.
 */
static inline paddr_t layout_text_end(void)
{
	extern uint8_t text_end[];
	return pa_init((uintpaddr_t)text_end);
}

/**
 * Get the address the .rodata section begins at.
 */
static inline paddr_t layout_rodata_begin(void)
{
	extern uint8_t rodata_begin[];
	return pa_init((uintpaddr_t)rodata_begin);
}

/**
 * Get the address the .rodata section ends at.
 */
static inline paddr_t layout_rodata_end(void)
{
	extern uint8_t rodata_end[];
	return pa_init((uintpaddr_t)rodata_end);
}

/**
 * Get the address the .data section begins at.
 */
static inline paddr_t layout_data_begin(void)
{
	extern uint8_t data_begin[];
	return pa_init((uintpaddr_t)data_begin);
}

/**
 * Get the address the .data section ends at.
 */
static inline paddr_t layout_data_end(void)
{
	extern uint8_t data_end[];
	return pa_init((uintpaddr_t)data_end);
}

/**
 * Get the address the loaded image ends at.
 */
static inline paddr_t layout_bin_end(void)
{
	extern uint8_t bin_end[];
	return pa_init((uintpaddr_t)bin_end);
}

/**
 * Get the address to load the primary VM at.
 *
 * This is placed just after the image.
 */
static inline paddr_t layout_primary_begin(void)
{
	/* TODO: This is a hack. We must read the alignment from the binary. */
	paddr_t bin_end = layout_bin_end();
	return pa_init((pa_addr(bin_end) + 0x80000 - 1) & ~(0x80000 - 1));
}
