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

#include "hf/addr.h"

paddr_t layout_text_begin(void);
paddr_t layout_text_end(void);

paddr_t layout_rodata_begin(void);
paddr_t layout_rodata_end(void);

paddr_t layout_data_begin(void);
paddr_t layout_data_end(void);

paddr_t layout_initrd_begin(void);
paddr_t layout_initrd_end(void);

paddr_t layout_fdt_begin(void);
paddr_t layout_fdt_end(void);

paddr_t layout_image_end(void);

paddr_t layout_primary_begin(void);
