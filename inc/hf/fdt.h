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
#include <stdint.h>

struct fdt_node {
	const struct fdt_header *hdr;
	const char *begin;
	const char *end;
	const char *strs;
};

size_t fdt_header_size(void);
uint32_t fdt_total_size(struct fdt_header *hdr);
void fdt_dump(struct fdt_header *hdr);
bool fdt_root_node(struct fdt_node *node, const struct fdt_header *hdr);
bool fdt_find_child(struct fdt_node *node, const char *child);
bool fdt_first_child(struct fdt_node *node, const char **child_name);
bool fdt_next_sibling(struct fdt_node *node, const char **sibling_name);
bool fdt_read_property(const struct fdt_node *node, const char *name,
		       const char **buf, uint32_t *size);

void fdt_add_mem_reservation(struct fdt_header *hdr, uint64_t addr,
			     uint64_t len);
