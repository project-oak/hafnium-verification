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

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "hf/dlog.h"
#include "hf/socket.h"

#include "hftest.h"
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/types.h>

#define MAX_BUF_SIZE 256

static int finit_module(int fd, const char *param_values, int flags)
{
	return syscall(SYS_finit_module, fd, param_values, flags);
}

static int delete_module(const char *name, int flags)
{
	return syscall(SYS_delete_module, name, flags);
}

static void insmod_hafnium(void)
{
	int module_file = open("/hafnium.ko", O_RDONLY);
	if (module_file < 0) {
		FAIL("Failed to load Hafnium kernel module from /hafnium.ko");
		return;
	}
	EXPECT_EQ(finit_module(module_file, "", 0), 0);
	close(module_file);
}

static void rmmod_hafnium(void)
{
	EXPECT_EQ(delete_module("hafnium", 0), 0);
}

/**
 * Loads and unloads the Hafnium kernel module.
 */
TEST(linux, load_hafnium)
{
	insmod_hafnium();
	rmmod_hafnium();
}

/**
 * Uses the kernel module to send a socket message from the primary VM to a
 * secondary VM and echoes it back to the primary.
 */
TEST(linux, socket_echo_hafnium)
{
	spci_vm_id_t vm_id = HF_VM_ID_OFFSET + 1;
	int port = 10;
	int socket_id;
	struct hf_sockaddr addr;
	const char send_buf[] = "The quick brown fox jumps over the lazy dogs.";
	size_t send_len = strlen(send_buf);
	char resp_buf[MAX_BUF_SIZE];
	ssize_t recv_len;

	ASSERT_LT(send_len, MAX_BUF_SIZE);

	insmod_hafnium();

	/* Create Hafnium socket. */
	socket_id = socket(PF_HF, SOCK_DGRAM, 0);
	if (socket_id == -1) {
		FAIL("Socket creation failed: %s", strerror(errno));
		return;
	}
	HFTEST_LOG("Socket created successfully.");

	/* Connect to requested VM & port. */
	addr.family = PF_HF;
	addr.vm_id = vm_id;
	addr.port = port;
	if (connect(socket_id, (struct sockaddr *)&addr, sizeof(addr)) == -1) {
		FAIL("Socket connection failed: %s", strerror(errno));
		return;
	}
	HFTEST_LOG("Socket to secondary VM %d connected on port %d.", vm_id,
		   port);

	/*
	 * Send a message to the secondary VM.
	 * Enable the confirm flag to try again in case port is busy.
	 */
	if (send(socket_id, send_buf, send_len, MSG_CONFIRM) < 0) {
		FAIL("Socket send() failed: %s", strerror(errno));
		return;
	}
	HFTEST_LOG("Packet with length %d sent.", send_len);

	/* Receive a response, which should be an echo of the sent packet. */
	recv_len = recv(socket_id, resp_buf, sizeof(resp_buf) - 1, 0);

	if (recv_len == -1) {
		FAIL("Socket recv() failed: %s", strerror(errno));
		return;
	}
	HFTEST_LOG("Packet with length %d received.", recv_len);

	EXPECT_EQ(recv_len, send_len);
	EXPECT_EQ(memcmp(send_buf, resp_buf, send_len), 0);

	EXPECT_EQ(close(socket_id), 0);
	rmmod_hafnium();
}
