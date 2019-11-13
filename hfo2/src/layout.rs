/*
 * Copyright 2019 Sanguk Park
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

use crate::addr::*;

extern "C" {
    pub fn layout_text_begin() -> paddr_t;
    pub fn layout_text_end() -> paddr_t;

    pub fn layout_rodata_begin() -> paddr_t;
    pub fn layout_rodata_end() -> paddr_t;

    pub fn layout_data_begin() -> paddr_t;
    pub fn layout_data_end() -> paddr_t;

    pub fn layout_initrd_begin() -> paddr_t;
    pub fn layout_initrd_end() -> paddr_t;

    pub fn layout_fdt_begin() -> paddr_t;
    pub fn layout_fdt_end() -> paddr_t;

    pub fn layout_image_end() -> paddr_t;

    pub fn layout_primary_begin() -> paddr_t;
}
