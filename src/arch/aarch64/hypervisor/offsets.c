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

#include "offsets.h"

#include "hf/cpu.h"
#include "hf/static_assert.h"

#define CHECK_OFFSET(name, type, field) \
	CHECK_OFFSET_1(#name, name, offsetof(type, field))
#define CHECK_OFFSET_1(name, actual, expected)               \
	static_assert((actual) == (expected),                \
		      "Offset " name " should be " #expected \
		      " and not " #actual)

CHECK_OFFSET(CPU_ID, struct cpu, id);
CHECK_OFFSET(CPU_STACK_BOTTOM, struct cpu, stack_bottom);
CHECK_OFFSET(VCPU_REGS, struct vcpu, regs);
CHECK_OFFSET(VCPU_LAZY, struct vcpu, regs.lazy);
CHECK_OFFSET(VCPU_FREGS, struct vcpu, regs.fp);

#ifdef VCPU_GIC
CHECK_OFFSET(VCPU_GIC, struct vcpu, regs.gic);
#endif
