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
#include <stdnoreturn.h>

enum power_status {
	POWER_STATUS_ON,
	POWER_STATUS_OFF,
	POWER_STATUS_ON_PENDING,
};

noreturn void arch_power_off(void);

bool cpu_start(uintptr_t id, void *stack, size_t stack_size,
	       void (*entry)(uintptr_t arg), uintptr_t arg);

noreturn void cpu_stop(void);
enum power_status cpu_status(uint64_t cpu_id);
