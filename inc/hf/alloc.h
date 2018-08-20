#pragma once

#include <stddef.h>

void halloc_init(size_t base, size_t size);
void *halloc(size_t size);
void hfree(void *ptr);
void *halloc_aligned(size_t size, size_t align);
void *halloc_aligned_nosync(size_t size, size_t align);
