/*
 * Copyright 2018 Google LLC
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

#ifndef GEN_OFFSETS
#include "offsets.h"
#endif /* GEN_OFFSETS */

#include "hf/cpu.h"
#include "hf/decl_offsets.h"

DECL(CPU_CURRENT, struct cpu, current);
DECL(CPU_STACK_BOTTOM, struct cpu, stack_bottom);
DECL(VCPU_REGS, struct vcpu, regs);
DECL(VCPU_LAZY, struct vcpu, regs.lazy);
