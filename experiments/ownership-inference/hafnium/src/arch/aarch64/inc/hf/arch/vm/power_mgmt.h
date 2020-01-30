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

#include "hf/arch/types.h"

enum power_status {
	POWER_STATUS_ON,
	POWER_STATUS_OFF,
	POWER_STATUS_ON_PENDING,
};

/**
 * Holds temporary state used to set up the environment on which CPUs will
 * start executing.
 *
 * vm_cpu_entry() depends on the layout of this struct.
 */
struct arch_cpu_start_state {
	uintptr_t initial_sp;
	void (*entry)(uintreg_t arg);
	uintreg_t arg;
};

bool arch_cpu_start(uintptr_t id, struct arch_cpu_start_state *s);

noreturn void arch_cpu_stop(void);
enum power_status arch_cpu_status(cpu_id_t cpu_id);

noreturn void arch_power_off(void);
