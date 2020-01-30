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

#include <stdalign.h>
#include <stdint.h>

#include "hf/memiter.h"
#include "hf/spci.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"
#include "vmapi/hf/transport.h"

#include "test/hftest.h"
#include "test/vmapi/spci.h"

alignas(4096) uint8_t kstack[4096];

static alignas(HF_MAILBOX_SIZE) uint8_t send[HF_MAILBOX_SIZE];
static alignas(HF_MAILBOX_SIZE) uint8_t recv[HF_MAILBOX_SIZE];

static hf_ipaddr_t send_addr = (hf_ipaddr_t)send;
static hf_ipaddr_t recv_addr = (hf_ipaddr_t)recv;

static struct hftest_context global_context;

struct hftest_context *hftest_get_context(void)
{
	return &global_context;
}

noreturn void abort(void)
{
	HFTEST_LOG("Service contained failures.");
	/* Cause a fault, as a secondary can't power down the machine. */
	*((volatile uint8_t *)1) = 1;

	/* This should never be reached, but to make the compiler happy... */
	for (;;) {
	}
}

static void swap(uint64_t *a, uint64_t *b)
{
	uint64_t t = *a;
	*a = *b;
	*b = t;
}

noreturn void kmain(size_t memory_size)
{
	struct hftest_context *ctx;

	/* Prepare the context. */

	/* Set up the mailbox. */
	spci_rxtx_map(send_addr, recv_addr);

	EXPECT_SPCI_ERROR(spci_rx_release(), SPCI_DENIED);

	/* Clean the context. */
	ctx = hftest_get_context();
	memset_s(ctx, sizeof(*ctx), 0, sizeof(*ctx));
	ctx->abort = abort;
	ctx->send = send;
	ctx->recv = recv;
	ctx->memory_size = memory_size;

	for (;;) {
		struct spci_value ret;

		/* Receive the packet. */
		ret = spci_msg_wait();
		EXPECT_EQ(ret.func, SPCI_MSG_SEND_32);
		EXPECT_LE(spci_msg_send_size(ret), SPCI_MSG_PAYLOAD_MAX);

		/* Echo the message back to the sender. */
		memcpy_s(send, SPCI_MSG_PAYLOAD_MAX, recv,
			 spci_msg_send_size(ret));

		/* Swap the socket's source and destination ports */
		struct hf_msg_hdr *hdr = (struct hf_msg_hdr *)send;
		swap(&(hdr->src_port), &(hdr->dst_port));

		/* Swap the destination and source ids. */
		spci_vm_id_t dst_id = spci_msg_send_sender(ret);
		spci_vm_id_t src_id = spci_msg_send_receiver(ret);

		EXPECT_EQ(spci_rx_release().func, SPCI_SUCCESS_32);
		EXPECT_EQ(spci_msg_send(src_id, dst_id, spci_msg_send_size(ret),
					0)
				  .func,
			  SPCI_SUCCESS_32);
	}
}
