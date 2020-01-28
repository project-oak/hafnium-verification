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

#include "vmapi/hf/spci.h"

bool exception_handler_skip_instruction(void);

bool exception_handler_yield_unknown(void);

bool exception_handler_yield_data_abort(void);

bool exception_handler_yield_instruction_abort(void);

int exception_handler_get_num(void);

void exception_handler_reset(void);

void exception_handler_send_exception_count(void);

int exception_handler_receive_exception_count(
	const struct spci_value *send_res,
	const struct spci_memory_region *recv_buf);
