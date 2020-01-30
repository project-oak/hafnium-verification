// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright 2019 The Hafnium Authors.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * version 2 as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 */

#pragma once

#include <linux/socket.h>

#include <hf/spci.h>

/* TODO: Reusing AF_ECONET for now as it's otherwise unused. */
#define AF_HF AF_ECONET
#define PF_HF AF_HF

/*
 * Address of a Hafnium socket
 */
struct hf_sockaddr {
	__kernel_sa_family_t family;
	spci_vm_id_t vm_id;
	uint64_t port;
};
