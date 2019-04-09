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
#define SPCI_VERSION_32               0x84000060
#define SPCI_MSG_BUF_LIST_EXCHANGE_32 0x84000061
#define SPCI_MSG_RECV_32              0x84000062
#define SPCI_MSG_PUT_32               0x84000063
#define SPCI_MSG_SEND_32              0x84000064
#define SPCI_MSG_SEND_REC_32          0x84000065
#define SPCI_RUN_32                   0x84000066
#define SPCI_YIELD_32                 0x84000067

/* SPCI return codes. */
#define SPCI_SUCCESS            INT32_C(0)
#define SPCI_NOT_SUPPORTED      INT32_C(-1)
#define SPCI_INVALID_PARAMETERS INT32_C(-2)
#define SPCI_NO_MEMORY          INT32_C(-3)
#define SPCI_BUSY               INT32_C(-4)
#define SPCI_INTERRUPTED        INT32_C(-5)
#define SPCI_DENIED             INT32_C(-6)
/* TODO: return code currently undefined in SPCI alpha2. */
#define SPCI_RETRY              INT32_C(-7)

/* Architected memory sharing message IDs. */
enum spci_memory_share {
	SPCI_MEMORY_DONATE = 0x2,
};

/* SPCI function specific constants. */
#define SPCI_MSG_RECV_BLOCK_MASK  0x1
#define SPCI_MSG_SEND_NOTIFY_MASK 0x1

#define SPCI_MESSAGE_ARCHITECTED 0x0
#define SPCI_MESSAGE_IMPDEF      0x1
#define SPCI_MESSAGE_IMPDEF_MASK 0x1

#define SPCI_MSG_SEND_NOTIFY 0x1
#define SPCI_MSG_RECV_BLOCK  0x1

/* The maximum length possible for a single message. */
#define SPCI_MSG_PAYLOAD_MAX (HF_MAILBOX_SIZE - sizeof(struct spci_message))

/* clang-format on */

/** The ID of a VM. These are assigned sequentially. */
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

/** Return type of SPCI functions. */
/* TODO: Reuse spci_return_t type on all SPCI functions declarations. */
typedef int32_t spci_return_t;

/** SPCI common message header. */
struct spci_message {
	/*
	 * TODO: version is part of SPCI alpha2 but will be
	 * removed in the next spec revision hence we are not
	 * including it in the header.
	 */

	/**
	 * flags[0]:
	 *     0: Architected message payload;
	 *     1: Implementation defined message payload.
	 * flags[15:1] reserved (MBZ).
	 */
	uint16_t flags;

	/*
	 * TODO: Padding is present to ensure controlled offset
	 * of the length field. SPCI spec must be updated
	 * to reflect this (TBD).
	 */
	uint16_t reserved_1;

	uint32_t length;
	spci_vm_id_t target_vm_id;
	spci_vm_id_t source_vm_id;

	/*
	 * TODO: Padding is present to ensure that the field
	 * payload alignment is 64B. SPCI spec must be updated
	 * to reflect this.
	 */
	uint32_t reserved_2;

	uint8_t payload[];
};

struct spci_architected_message_header {
	uint16_t type;

	/*
	 * TODO: Padding is present to ensure that the field
	 * payload is aligned on a 64B boundary. SPCI
	 * spec must be updated to reflect this.
	 */
	uint16_t reserved[3];
	uint8_t payload[];
};

struct spci_memory_region_constituent {
	uint64_t address;
	uint32_t page_count;

	uint32_t reserved;
};

struct spci_memory_region {
	spci_memory_handle_t handle;
	uint32_t count;

	struct spci_memory_region_constituent constituents[];
};

/* TODO: Move all the functions below this line to a support library. */
/**
 * Fill all the fields, except for the flags, in the SPCI message common header.
 */
static inline void spci_common_header_init(struct spci_message *message,
					   uint32_t message_length,
					   spci_vm_id_t target_vm_id,
					   spci_vm_id_t source_vm_id)
{
	message->length = message_length;
	message->target_vm_id = target_vm_id;
	message->source_vm_id = source_vm_id;

	/*
	 * TODO: Reserved fields in the common message header will be
	 * defined as MBZ in next SPCI spec updates.
	 */
	message->reserved_1 = 0;
	message->reserved_2 = 0;
}

/**
 * Set the SPCI implementation defined message header fields.
 */
static inline void spci_message_init(struct spci_message *message,
				     uint32_t message_length,
				     spci_vm_id_t target_vm_id,
				     spci_vm_id_t source_vm_id)
{
	spci_common_header_init(message, message_length, target_vm_id,
				source_vm_id);

	message->flags = SPCI_MESSAGE_IMPDEF;
}

/**
 * Obtain a pointer to the architected header in the spci_message.
 *
 * Note: the argument "message" has const qualifier. This qualifier
 * is meant to forbid changes in information enclosed in the
 * struct spci_message. The spci_architected_message_header, for which
 * a pointer is returned in this function, is not part of spci_message.
 * Its information is meant to be changed and hence the returned pointer
 * does not have const type qualifier.
 */
static inline struct spci_architected_message_header *
spci_get_architected_message_header(const struct spci_message *message)
{
	return (struct spci_architected_message_header *)message->payload;
}

/**
 * Helper method to fill in the information about the architected message.
 */
static inline void spci_architected_message_init(struct spci_message *message,
						 uint32_t message_length,
						 spci_vm_id_t target_vm_id,
						 spci_vm_id_t source_vm_id,
						 enum spci_memory_share type)
{
	struct spci_architected_message_header *architected_header;

	spci_common_header_init(message, message_length, target_vm_id,
				source_vm_id);
	message->flags = SPCI_MESSAGE_ARCHITECTED;

	/* Fill the architected header. */
	architected_header = spci_get_architected_message_header(message);
	architected_header->type = type;
	architected_header->reserved[0] = 0;
	architected_header->reserved[1] = 0;
	architected_header->reserved[2] = 0;
}

/** Obtain a pointer to the start of the memory region in the donate message. */
static inline struct spci_memory_region *spci_get_donated_memory_region(
	struct spci_message *message)
{
	struct spci_architected_message_header *architected_header =
		spci_get_architected_message_header(message);
	return (struct spci_memory_region *)architected_header->payload;
}

/**
 * Add a memory region to the current message.
 * A memory region is composed of one or more constituents.
 */
static inline void spci_memory_region_add(
	struct spci_message *message, spci_memory_handle_t handle,
	const struct spci_memory_region_constituent constituents[],
	uint32_t num_constituents)
{
	struct spci_memory_region *memory_region =
		spci_get_donated_memory_region(message);

	uint32_t constituents_length =
		num_constituents *
		sizeof(struct spci_memory_region_constituent);
	uint32_t index;

	memory_region->handle = handle;
	memory_region->count = num_constituents;

	for (index = 0; index < num_constituents; index++) {
		memory_region->constituents[index] = constituents[index];
		memory_region->constituents[index].reserved = 0;
	}

	/*
	 * TODO: Add assert ensuring that the specified message
	 * length is not greater than SPCI_MSG_PAYLOAD_MAX.
	 */
	message->length +=
		sizeof(struct spci_memory_region) + constituents_length;
}

/** Construct the SPCI donate memory region message. */
static inline void spci_memory_donate(
	struct spci_message *message, spci_vm_id_t target_vm_id,
	spci_vm_id_t source_vm_id,
	struct spci_memory_region_constituent *region_constituents,
	uint32_t num_elements, uint32_t handle)
{
	int32_t message_length;

	message_length = sizeof(struct spci_architected_message_header);

	/* Fill in the details on the common message header. */
	spci_architected_message_init(message, message_length, target_vm_id,
				      source_vm_id, SPCI_MEMORY_DONATE);

	/* Create single memory region. */
	spci_memory_region_add(message, handle, region_constituents,
			       num_elements);
}
