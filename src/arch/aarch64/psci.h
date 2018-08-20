#pragma once

/* clang-format off */

#define PSCI_CONVENTION_MASK (1u << 30)

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
#define PSCI_RETURN_NOT_SUPPORTED      (-1)
#define PSCI_RETURN_INVALID_PARAMETERS (-2)
#define PSCI_RETURN_DENIED             (-3)
#define PSCI_RETURN_ALREADY_ON         (-4)
#define PSCI_RETURN_ON_PENDING         (-5)
#define PSCI_RETURN_INTERNAL_FAILURE   (-6)
#define PSCI_NOT_PRESENT               (-7)
#define PSCI_DISABLE                   (-8)
#define PSCI_INVALID_ADDRESS           (-9)

/* clang-format on */
