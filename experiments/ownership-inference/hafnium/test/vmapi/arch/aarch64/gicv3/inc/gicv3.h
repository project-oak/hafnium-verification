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

#include "hf/addr.h"
#include "hf/mm.h"
#include "hf/types.h"

#define PPI_IRQ_BASE 16
#define PHYSICAL_TIMER_IRQ (PPI_IRQ_BASE + 14)
#define VIRTUAL_TIMER_IRQ (PPI_IRQ_BASE + 11)
#define HYPERVISOR_TIMER_IRQ (PPI_IRQ_BASE + 10)

#define NANOS_PER_UNIT 1000000000

#define SERVICE_VM1 (HF_VM_ID_OFFSET + 1)

extern alignas(PAGE_SIZE) uint8_t send_page[PAGE_SIZE];
extern alignas(PAGE_SIZE) uint8_t recv_page[PAGE_SIZE];

extern hf_ipaddr_t send_page_addr;
extern hf_ipaddr_t recv_page_addr;

extern void *send_buffer;
extern void *recv_buffer;

extern volatile uint32_t last_interrupt_id;

void system_setup();
