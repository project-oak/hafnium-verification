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

#include "hf/types.h"

#pragma once

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

/* SPCI function specific constants. */
#define SPCI_MSG_RECV_BLOCK_MASK  0x1
#define SPCI_MSG_SEND_NOTIFY_MASK 0x1

#define SPCI_MESSAGE_IMPDEF_MASK 0x1

#define SPCI_MSG_SEND_NOTIFY 0x1
#define SPCI_MSG_RECV_BLOCK  0x1

/* The maximum length possible for a single message. */
#define SPCI_MSG_PAYLOAD_MAX (HF_MAILBOX_SIZE - sizeof(struct spci_message))

/* clang-format on */

/** The ID of a VM. These are assigned sequentially. */
typedef uint16_t spci_vm_id_t;

/**
 * A count of VMs. This has the same range as the VM IDs but we give it a
 * different name to make the different semantics clear.
 */
typedef spci_vm_id_t spci_vm_count_t;
typedef uint16_t spci_vcpu_index_t;

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

/**
 * Set the SPCI common message header fields.
 */
static inline void spci_message_init(struct spci_message *message,
				     uint32_t message_length,
				     spci_vm_id_t target_vm_id,
				     spci_vm_id_t source_vm_id)
{
	message->flags = SPCI_MESSAGE_IMPDEF_MASK;
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
