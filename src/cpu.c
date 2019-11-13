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

#include "hf/cpu.h"

#include <stdalign.h>

#include "hf/arch/cpu.h"

#include "hf/api.h"
#include "hf/check.h"
#include "hf/dlog.h"
#include "hf/spci.h"
#include "hf/std.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"

#define STACK_SIZE PAGE_SIZE

/* The stack to be used by the CPUs. */
alignas(2 * sizeof(uintreg_t)) char callstacks[MAX_CPUS][STACK_SIZE];

/**
 * A temporal variable for one-time booting sequence. The booting CPU will
 * refer this.
 */
struct cpu boot_cpu = {
	.stack_bottom = &callstacks[0][STACK_SIZE],
};
