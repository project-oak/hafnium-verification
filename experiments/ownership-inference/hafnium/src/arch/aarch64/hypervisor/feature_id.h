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

#include "hf/arch/types.h"

#include "hf/cpu.h"

#include "vmapi/hf/spci.h"

#define HF_FEATURE_NONE UINT64_C(0)

/*  Reliability, Availability, and Serviceability (RAS) Extension Features */
#define HF_FEATURE_RAS UINT64_C(1)

/* Limited Ordering Regions */
#define HF_FEATURE_LOR (UINT64_C(1) << 1)

/* Performance Monitor */
#define HF_FEATURE_PERFMON (UINT64_C(1) << 2)

/* Debug Registers */
#define HF_FEATURE_DEBUG (UINT64_C(1) << 3)

/* Statistical Profiling Extension (SPE) */
#define HF_FEATURE_SPE (UINT64_C(1) << 4)

/* Self-hosted Trace */
#define HF_FEATURE_TRACE (UINT64_C(1) << 5)

/* Pointer Authentication (PAuth) */
#define HF_FEATURE_PAUTH (UINT64_C(1) << 6)

/*
 * NOTE: This should be based on the last (highest value) defined feature.
 * Adjust if adding more features.
 */
#define HF_FEATURE_ALL ((HF_FEATURE_PAUTH << 1) - 1)

bool feature_id_is_register_access(uintreg_t esr_el2);

bool feature_id_process_access(struct vcpu *vcpu, uintreg_t esr_el2);

void feature_set_traps(struct vm *vm, struct arch_regs *regs);
