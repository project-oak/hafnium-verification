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

/**
 * Set to disable cycle counting when event counting is prohibited.
 */
#define PMCR_EL0_DP 0x10

/**
 * Set to enable export of events where not prohibited.
 */
#define PMCR_EL0_X 0x8

/**
 * Set to enable event counting.
 */
#define PMCR_EL0_E 0x1

/**
 * Set to disable cycle counting in EL1.
 */
#define PMCCFILTR_EL0_P 0x80000000

/**
 * Set to disable cycle counting in EL0.
 */
#define PMCCFILTR_EL0_U 0x40000000

/**
 * Cycle counting in non-secure EL1 is enabled if NSK == P.
 */
#define PMCCFILTR_EL0_NSK 0x20000000

/**
 * Cycle counting in non-secure EL0 is enabled if NSU == U.
 */
#define PMCCFILTR_EL0_NSU 0x10000000

/**
 * Set to enable cycle counting in EL2.
 */
#define PMCCFILTR_EL0_NSH 0x8000000

/**
 * Cycle counting in EL3 is enabled if M == P.
 */
#define PMCCFILTR_EL0_M 0x4000000

/**
 * Cycle counting in Secutre EL2 is enabled if SH != NSH.
 */
#define PMCCFILTR_EL0_SH 0x1000000

bool perfmon_is_register_access(uintreg_t esr_el2);

bool perfmon_process_access(struct vcpu *vcpu, spci_vm_id_t vm_id,
			    uintreg_t esr_el2);

uintreg_t perfmon_get_pmccfiltr_el0_init_value(spci_vm_id_t vm_id);
