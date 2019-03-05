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

#include <stdalign.h>
#include <stdint.h>

#include "hf/arch/std.h"

#include "hf/memiter.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

alignas(4096) uint8_t kstack[4096];

HFTEST_ENABLE();

extern struct hftest_test hftest_begin[];
extern struct hftest_test hftest_end[];

static alignas(HF_MAILBOX_SIZE) uint8_t send[HF_MAILBOX_SIZE];
static alignas(HF_MAILBOX_SIZE) uint8_t recv[HF_MAILBOX_SIZE];

static hf_ipaddr_t send_addr = (hf_ipaddr_t)send;
static hf_ipaddr_t recv_addr = (hf_ipaddr_t)recv;

static struct hftest_context global_context;

struct hftest_context *hftest_get_context(void)
{
	return &global_context;
}

/** Find the service with the name passed in the arguments. */
static hftest_test_fn find_service(struct memiter *args)
{
	struct memiter service_name;
	struct hftest_test *test;

	if (!memiter_parse_str(args, &service_name)) {
		return NULL;
	}

	for (test = hftest_begin; test < hftest_end; ++test) {
		if (test->kind == HFTEST_KIND_SERVICE &&
		    memiter_iseq(&service_name, test->name)) {
			return test->fn;
		}
	}

	return NULL;
}

static noreturn void abort(void)
{
	HFTEST_LOG("Service contained failures.");
	for (;;) {
		/*
		 * Hang if the service aborts as a secondary can't power down
		 * the machine.
		 */
	}
}

noreturn void kmain(void)
{
	struct memiter args;
	hftest_test_fn service;
	struct hf_mailbox_receive_return res;
	struct hftest_context *ctx;

	/* Prepare the context. */

	/* Set up the mailbox. */
	hf_vm_configure(send_addr, recv_addr);

	/* Receive the name of the service to run. */
	res = hf_mailbox_receive(true);
	memiter_init(&args, recv, res.size);
	service = find_service(&args);
	hf_mailbox_clear();

	/* Check the service was found. */
	if (service == NULL) {
		HFTEST_LOG_FAILURE();
		HFTEST_LOG(HFTEST_LOG_INDENT
			   "Unable to find requested service");
		for (;;) {
			/* Hang if the service was unknown. */
		}
	}

	/* Clean the context. */
	ctx = hftest_get_context();
	memset(ctx, 0, sizeof(*ctx));
	ctx->abort = abort;
	ctx->send = send;
	ctx->recv = recv;

	/* Pause so the next time cycles are given the service will be run. */
	hf_vcpu_yield();

	/* Let the service run. */
	service();

	/* Cleanly handle it if the service returns. */
	if (ctx->failures) {
		abort();
	}

	for (;;) {
		/* Hang if the service returns. */
	}
}
