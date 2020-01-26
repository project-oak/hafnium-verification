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

#include "hf/fdt.h"
#include "hf/memiter.h"

#include "test/hftest_impl.h"

void hftest_use_registered_list(void);
void hftest_use_list(struct hftest_test list[], size_t count);

void hftest_json(void);
void hftest_run(struct memiter suite_name, struct memiter test_name,
		const struct fdt_header *fdt);
void hftest_help(void);
