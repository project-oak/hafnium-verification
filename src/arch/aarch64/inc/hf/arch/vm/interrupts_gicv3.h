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

#pragma once

#include <stdbool.h>
#include <stdint.h>

#if GIC_VERSION != 3 && GIC_VERSION != 4
#error This header should only be included for GICv3 or v4.
#endif

#define SGI_BASE (GICR_BASE + 0x10000)

#define GICD_CTLR (*(volatile uint32_t *)(GICD_BASE + 0x0000))
#define GICD_ISENABLER(n) (((volatile uint32_t *)(GICD_BASE + 0x0100))[n])
#define GICD_ICENABLER(n) (((volatile uint32_t *)(GICD_BASE + 0x0180))[n])
#define GICD_ISPENDR(n) (((volatile uint32_t *)(GICD_BASE + 0x0200))[n])
#define GICD_ICPENDR(n) (((volatile uint32_t *)(GICD_BASE + 0x0280))[n])
#define GICD_ISACTIVER(n) (((volatile uint32_t *)(GICD_BASE + 0x0300))[n])
#define GICD_ICACTIVER(n) (((volatile uint32_t *)(GICD_BASE + 0x0380))[n])
#define GICD_IPRIORITYR(n) (((volatile uint8_t *)(GICD_BASE + 0x0400))[n])
#define GICD_ITARGETSR(n) (((volatile uint32_t *)(GICD_BASE + 0x0800))[n])
#define GICD_ICFGR(n) (((volatile uint32_t *)(GICD_BASE + 0x0c00))[n])
#define GICR_WAKER (*(volatile uint32_t *)(GICR_BASE + 0x0014))
#define GICR_IGROUPR0 (*(volatile uint32_t *)(SGI_BASE + 0x0080))
#define GICR_ISENABLER0 (*(volatile uint32_t *)(SGI_BASE + 0x0100))
#define GICR_ICENABLER0 (*(volatile uint32_t *)(SGI_BASE + 0x0180))
#define GICR_ISPENDR0 (*(volatile uint32_t *)(SGI_BASE + 0x0200))
#define GICR_ICPENDR0 (*(volatile uint32_t *)(SGI_BASE + 0x0280))
#define GICR_ISACTIVER0 (*(volatile uint32_t *)(SGI_BASE + 0x0300))
#define GICR_ICFGR(n) (((volatile uint32_t *)(SGI_BASE + 0x0c00))[n])

void exception_setup(void);
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
