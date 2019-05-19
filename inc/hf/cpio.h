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

#include "hf/memiter.h"

bool cpio_next(struct memiter *iter, const char **name, const void **contents,
	       size_t *size);
bool cpio_find_file_memiter(const struct memiter *cpio,
                            const struct memiter *filename,
                            struct memiter *it);
bool cpio_find_file(const struct memiter *cpio,
                    const char *name,
                    struct memiter *it);
