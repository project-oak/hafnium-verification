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

/* clang-format off */

#define SMCCC_CALL_TYPE_MASK  0x80000000
#define SMCCC_YIELDING_CALL   0x00000000
#define SMCCC_FAST_CALL       0x80000000

#define SMCCC_CONVENTION_MASK 0x40000000
#define SMCCC_32_BIT          0x00000000
#define SMCCC_64_BIT          0x40000000

#define SMCCC_SERVICE_CALL_MASK                0x3f000000
#define SMCCC_ARM_ARCHITECTURE_CALL            0x00000000
#define SMCCC_CPU_SERVICE_CALL                 0x01000000
#define SMCCC_SIP_SERVICE_CALL                 0x02000000
#define SMCCC_OEM_SERVICE_CALL                 0x03000000
#define SMCCC_STANDARD_SECURE_SERVICE_CALL     0x04000000
#define SMCCC_STANDARD_HYPERVISOR_SERVICE_CALL 0x05000000
#define SMCCC_VENDOR_HYPERVISOR_SERVICE_CALL   0x06000000
/*
 * TODO: Trusted application call: 0x30000000 - 0x31000000
 * TODO: Trusted OS call: 0x32000000 - 0x3f000000
 */

#define SMCCC_RETURN_UNKNOWN  (-1)

/* The following are PSCI version codes. */
#define PSCI_VERSION_0_2 0x00000002
#define PSCI_VERSION_1_0 0x00010000
#define PSCI_VERSION_1_1 0x00010001

/* The following are function identifiers for PSCI. */
#define PSCI_VERSION                 0x84000000
#define PSCI_CPU_SUSPEND             0x84000001
#define PSCI_CPU_OFF                 0x84000002
#define PSCI_CPU_ON                  0x84000003
#define PSCI_AFFINITY_INFO           0x84000004
#define PSCI_MIGRATE                 0x84000005
#define PSCI_MIGRATE_INFO_TYPE       0x84000006
#define PSCI_MIGRATE_INFO_UP_CPU     0x84000007
#define PSCI_SYSTEM_OFF              0x84000008
#define PSCI_SYSTEM_RESET            0x84000009
#define PSCI_FEATURES                0x8400000a
#define PSCI_CPU_FREEZE              0x8400000b
#define PSCI_CPU_DEFAULT_SUSPEND     0x8400000c
#define PSCI_NODE_HW_STATE           0x8400000d
#define PSCI_SYSTEM_SUSPEND          0x8400000e
#define PSCI_SET_SYSPEND_MODE        0x8400000f
#define PSCI_STAT_RESIDENCY          0x84000010
#define PSCI_STAT_COUNT              0x84000011
#define PSCI_SYSTEM_RESET2           0x84000012
#define PSCI_MEM_PROTECT             0x84000013
#define PSCI_MEM_PROTECT_CHECK_RANGE 0x84000014

/* The following are return codes for PSCI. */
#define PSCI_RETURN_SUCCESS            0
#define PSCI_RETURN_NOT_SUPPORTED      SMCCC_RETURN_UNKNOWN
#define PSCI_RETURN_INVALID_PARAMETERS (-2)
#define PSCI_RETURN_DENIED             (-3)
#define PSCI_RETURN_ALREADY_ON         (-4)
#define PSCI_RETURN_ON_PENDING         (-5)
#define PSCI_RETURN_INTERNAL_FAILURE   (-6)
#define PSCI_NOT_PRESENT               (-7)
#define PSCI_DISABLE                   (-8)
#define PSCI_INVALID_ADDRESS           (-9)

/* clang-format on */
