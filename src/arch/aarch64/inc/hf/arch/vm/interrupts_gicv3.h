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

#include <stdbool.h>
#include <stdint.h>

#include "hf/io.h"

#if GIC_VERSION != 3 && GIC_VERSION != 4
#error This header should only be included for GICv3 or v4.
#endif

/* Keep macro alignment */
/* clang-format off */

#define SGI_BASE (GICR_BASE + 0x10000)

#define GICD_CTLR       IO32_C(GICD_BASE + 0x0000)
#define GICD_ISENABLER  IO32_ARRAY_C(GICD_BASE + 0x0100, 32)
#define GICD_ICENABLER  IO32_ARRAY_C(GICD_BASE + 0x0180, 32)
#define GICD_ISPENDR    IO32_ARRAY_C(GICD_BASE + 0x0200, 32)
#define GICD_ICPENDR    IO32_ARRAY_C(GICD_BASE + 0x0280, 32)
#define GICD_ISACTIVER  IO32_ARRAY_C(GICD_BASE + 0x0300, 32)
#define GICD_ICACTIVER  IO32_ARRAY_C(GICD_BASE + 0x0380, 32)
#define GICD_IPRIORITYR IO8_ARRAY_C(GICD_BASE + 0x0400, 1020)
#define GICD_ITARGETSR  IO8_ARRAY_C(GICD_BASE + 0x0800, 1020)
#define GICD_ICFGR      IO32_ARRAY_C(GICD_BASE + 0x0c00, 64)
#define GICR_WAKER      IO32_C(GICR_BASE + 0x0014)
#define GICR_IGROUPR0   IO32_C(SGI_BASE + 0x0080)
#define GICR_ISENABLER0 IO32_C(SGI_BASE + 0x0100)
#define GICR_ICENABLER0 IO32_C(SGI_BASE + 0x0180)
#define GICR_ISPENDR0   IO32_C(SGI_BASE + 0x0200)
#define GICR_ICPENDR0   IO32_C(SGI_BASE + 0x0280)
#define GICR_ISACTIVER0 IO32_C(SGI_BASE + 0x0300)
#define GICR_ICFGR      IO32_ARRAY_C(SGI_BASE + 0x0c00, 32)

/* clang-format on */

void exception_setup(void (*irq)(void));
void interrupt_gic_setup(void);
void interrupt_enable(uint32_t intid, bool enable);
void interrupt_enable_all(bool enable);
void interrupt_set_priority_mask(uint8_t min_priority);
void interrupt_set_priority(uint32_t intid, uint8_t priority);
void interrupt_set_edge_triggered(uint32_t intid, bool edge_triggered);
void interrupt_send_sgi(uint8_t intid, bool irm, uint8_t affinity3,
			uint8_t affinity2, uint8_t affinity1,
			uint16_t target_list);
uint32_t interrupt_get_and_acknowledge(void);
void interrupt_end(uint32_t intid);
void interrupt_wait(void);
