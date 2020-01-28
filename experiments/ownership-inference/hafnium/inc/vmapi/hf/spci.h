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

#include "hf/types.h"

/* clang-format off */

#define SPCI_LOW_32_ID  0x84000060
#define SPCI_HIGH_32_ID 0x8400007F
#define SPCI_LOW_64_ID  0xC4000060
#define SPCI_HIGH_32_ID 0x8400007F

/* SPCI function identifiers. */
#define SPCI_ERROR_32                 0x84000060
#define SPCI_SUCCESS_32               0x84000061
#define SPCI_INTERRUPT_32             0x84000062
#define SPCI_VERSION_32               0x84000063
#define SPCI_FEATURES_32              0x84000064
#define SPCI_RX_RELEASE_32            0x84000065
#define SPCI_RXTX_MAP_32              0x84000066
#define SPCI_RXTX_MAP_64              0xC4000066
#define SPCI_RXTX_UNMAP_32            0x84000067
#define SPCI_PARTITION_INFO_GET_32    0x84000068
#define SPCI_ID_GET_32                0x84000069
#define SPCI_MSG_POLL_32              0x8400006A
#define SPCI_MSG_WAIT_32              0x8400006B
#define SPCI_YIELD_32                 0x8400006C
#define SPCI_RUN_32                   0x8400006D
#define SPCI_MSG_SEND_32              0x8400006E
#define SPCI_MSG_SEND_DIRECT_REQ_32   0x8400006F
#define SPCI_MSG_SEND_DIRECT_RESP_32  0x84000070
#define SPCI_MEM_DONATE_32            0x84000071
#define SPCI_MEM_LEND_32              0x84000072
#define SPCI_MEM_SHARE_32             0x84000073

/* SPCI error codes. */
#define SPCI_NOT_SUPPORTED      INT32_C(-1)
#define SPCI_INVALID_PARAMETERS INT32_C(-2)
#define SPCI_NO_MEMORY          INT32_C(-3)
#define SPCI_BUSY               INT32_C(-4)
#define SPCI_INTERRUPTED        INT32_C(-5)
#define SPCI_DENIED             INT32_C(-6)
#define SPCI_RETRY              INT32_C(-7)
#define SPCI_ABORTED            INT32_C(-8)

/* SPCI function specific constants. */
#define SPCI_MSG_RECV_BLOCK  0x1
#define SPCI_MSG_RECV_BLOCK_MASK  0x1

#define SPCI_MSG_SEND_NOTIFY 0x1
#define SPCI_MSG_SEND_NOTIFY_MASK 0x1

#define SPCI_SLEEP_INDEFINITE 0

/**
 * For use where the SPCI specification refers explicitly to '4K pages'. Not to
 * be confused with PAGE_SIZE, which is the translation granule Hafnium is
 * configured to use.
 */
#define SPCI_PAGE_SIZE 4096

/* The maximum length possible for a single message. */
#define SPCI_MSG_PAYLOAD_MAX HF_MAILBOX_SIZE

enum spci_memory_access {
	SPCI_MEMORY_RO_NX,
	SPCI_MEMORY_RO_X,
	SPCI_MEMORY_RW_NX,
	SPCI_MEMORY_RW_X,
};

enum spci_memory_type {
	SPCI_MEMORY_DEVICE_MEM,
	SPCI_MEMORY_NORMAL_MEM,
};

enum spci_memory_cacheability {
	SPCI_MEMORY_CACHE_RESERVED = 0x0,
	SPCI_MEMORY_CACHE_NON_CACHEABLE = 0x1,
	SPCI_MEMORY_CACHE_WRITE_THROUGH = 0x2,
	SPCI_MEMORY_CACHE_WRITE_BACK = 0x4,
	SPCI_MEMORY_DEV_NGNRNE = 0x0,
	SPCI_MEMORY_DEV_NGNRE = 0x1,
	SPCI_MEMORY_DEV_NGRE = 0x2,
	SPCI_MEMORY_DEV_GRE = 0x3,
};

enum spci_memory_shareability {
	SPCI_MEMORY_SHARE_NON_SHAREABLE,
	SPCI_MEMORY_RESERVED,
	SPCI_MEMORY_OUTER_SHAREABLE,
	SPCI_MEMORY_INNER_SHAREABLE,
};

#define SPCI_MEMORY_ACCESS_OFFSET (0x5U)
#define SPCI_MEMORY_ACCESS_MASK ((0x3U) << SPCI_MEMORY_ACCESS_OFFSET)

#define SPCI_MEMORY_TYPE_OFFSET (0x4U)
#define SPCI_MEMORY_TYPE_MASK ((0x1U) << SPCI_MEMORY_TYPE_OFFSET)

#define SPCI_MEMORY_CACHEABILITY_OFFSET (0x2U)
#define SPCI_MEMORY_CACHEABILITY_MASK ((0x3U) <<\
	SPCI_MEMORY_CACHEABILITY_OFFSET)

#define SPCI_MEMORY_SHAREABILITY_OFFSET (0x0U)
#define SPCI_MEMORY_SHAREABILITY_MASK ((0x3U) <<\
	SPCI_MEMORY_SHAREABILITY_OFFSET)

#define LEND_ATTR_FUNCTION_SET(name, offset, mask) \
static inline void spci_set_memory_##name##_attr(uint16_t *attr,\
	const enum spci_memory_##name perm)\
{\
	*attr = (*attr & ~(mask)) | ((perm  << offset) & mask);\
}

#define LEND_ATTR_FUNCTION_GET(name, offset, mask) \
static inline enum spci_memory_##name spci_get_memory_##name##_attr(\
	uint16_t attr)\
{\
	return (enum spci_memory_##name)((attr & mask) >> offset);\
}

LEND_ATTR_FUNCTION_SET(access, SPCI_MEMORY_ACCESS_OFFSET,
	SPCI_MEMORY_ACCESS_MASK)
LEND_ATTR_FUNCTION_GET(access, SPCI_MEMORY_ACCESS_OFFSET,
	SPCI_MEMORY_ACCESS_MASK)

LEND_ATTR_FUNCTION_SET(type, SPCI_MEMORY_TYPE_OFFSET, SPCI_MEMORY_TYPE_MASK)
LEND_ATTR_FUNCTION_GET(type, SPCI_MEMORY_TYPE_OFFSET, SPCI_MEMORY_TYPE_MASK)

LEND_ATTR_FUNCTION_SET(cacheability, SPCI_MEMORY_CACHEABILITY_OFFSET,
	SPCI_MEMORY_CACHEABILITY_MASK)

LEND_ATTR_FUNCTION_GET(cacheability, SPCI_MEMORY_CACHEABILITY_OFFSET,
	SPCI_MEMORY_CACHEABILITY_MASK)

LEND_ATTR_FUNCTION_SET(shareability, SPCI_MEMORY_SHAREABILITY_OFFSET,
	SPCI_MEMORY_SHAREABILITY_MASK)

LEND_ATTR_FUNCTION_GET(shareability, SPCI_MEMORY_SHAREABILITY_OFFSET,
	SPCI_MEMORY_SHAREABILITY_MASK)

/* clang-format on */

/** The ID of a VM. These are assigned sequentially starting with an offset. */
typedef uint16_t spci_vm_id_t;
typedef uint32_t spci_memory_handle_t;

/**
 * A count of VMs. This has the same range as the VM IDs but we give it a
 * different name to make the different semantics clear.
 */
typedef spci_vm_id_t spci_vm_count_t;

/** The index of a vCPU within a particular VM. */
typedef uint16_t spci_vcpu_index_t;

/**
 * A count of vCPUs. This has the same range as the vCPU indices but we give it
 * a different name to make the different semantics clear.
 */
typedef spci_vcpu_index_t spci_vcpu_count_t;

/** Parameter and return type of SPCI functions. */
struct spci_value {
	uint64_t func;
	uint64_t arg1;
	uint64_t arg2;
	uint64_t arg3;
	uint64_t arg4;
	uint64_t arg5;
	uint64_t arg6;
	uint64_t arg7;
};

static inline spci_vm_id_t spci_msg_send_sender(struct spci_value args)
{
	return (args.arg1 >> 16) & 0xffff;
}

static inline spci_vm_id_t spci_msg_send_receiver(struct spci_value args)
{
	return args.arg1 & 0xffff;
}

static inline uint32_t spci_msg_send_size(struct spci_value args)
{
	return args.arg3;
}

static inline uint32_t spci_msg_send_attributes(struct spci_value args)
{
	return args.arg4;
}

static inline spci_vm_id_t spci_vm_id(struct spci_value args)
{
	return (args.arg1 >> 16) & 0xffff;
}

static inline spci_vcpu_index_t spci_vcpu_index(struct spci_value args)
{
	return args.arg1 & 0xffff;
}

static inline uint64_t spci_vm_vcpu(spci_vm_id_t vm_id,
				    spci_vcpu_index_t vcpu_index)
{
	return ((uint32_t)vm_id << 16) | vcpu_index;
}

struct spci_memory_region_constituent {
	/**
	 * The base IPA of the constituent memory region, aligned to 4 kiB page
	 * size granularity.
	 */
	uint64_t address;
	/** The number of 4 kiB pages in the constituent memory region. */
	uint32_t page_count;

	uint32_t reserved;
};

struct spci_memory_region_attributes {
	/** The ID of the VM to which the memory is being given or shared. */
	spci_vm_id_t receiver;
	/**
	 * The attributes with which the memory region should be mapped in the
	 * receiver's page table.
	 */
	uint16_t memory_attributes;
};

/** Flags to control the behaviour of a memory sharing transaction. */
typedef uint32_t spci_memory_region_flags_t;

/**
 * Clear memory region contents after unmapping it from the sender and before
 * mapping it for any receiver.
 */
#define SPCI_MEMORY_REGION_FLAG_CLEAR 0x1

struct spci_memory_region {
	/**
	 * An implementation defined value associated with the receiver and the
	 * memory region.
	 */
	uint32_t tag;
	/** Flags to control behaviour of the transaction. */
	spci_memory_region_flags_t flags;
	/** Sender VM ID. */
	spci_vm_id_t sender;
	/** Reserved field, must be 0. */
	uint16_t reserved;
	/**
	 * The total number of 4 kiB pages included in this memory region. This
	 * must be equal to the sum of page counts specified in each
	 * `spci_memory_region_constituent`.
	 */
	uint32_t page_count;
	/**
	 * The number of constituents (`spci_memory_region_constituent`)
	 * included in this memory region.
	 */
	uint32_t constituent_count;
	/**
	 * The offset in bytes from the base address of this
	 * `spci_memory_region` to the start of the first
	 * `spci_memory_region_constituent`.
	 */
	uint32_t constituent_offset;
	/**
	 * The number of `spci_memory_region_attributes` entries included in
	 * this memory region.
	 */
	uint32_t attribute_count;
	/**
	 * An array of `attribute_count` memory region attribute descriptors.
	 * Each one specifies an endpoint and the attributes with which this
	 * memory region should be mapped in that endpoint's page table.
	 */
	struct spci_memory_region_attributes attributes[];
};

/**
 * Gets the constituent array for an `spci_memory_region`.
 */
static inline struct spci_memory_region_constituent *
spci_memory_region_get_constituents(struct spci_memory_region *memory_region)
{
	return (struct spci_memory_region_constituent
			*)((uint8_t *)memory_region +
			   memory_region->constituent_offset);
}

uint32_t spci_memory_region_init(
	struct spci_memory_region *memory_region, spci_vm_id_t sender,
	spci_vm_id_t receiver,
	const struct spci_memory_region_constituent constituents[],
	uint32_t constituent_count, uint32_t tag,
	spci_memory_region_flags_t flags, enum spci_memory_access access,
	enum spci_memory_type type, enum spci_memory_cacheability cacheability,
	enum spci_memory_shareability shareability);
