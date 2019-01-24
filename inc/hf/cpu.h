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
#include <stddef.h>
#include <stdint.h>

#include "hf/arch/cpu.h"

#include "hf/addr.h"
#include "hf/spinlock.h"

#include "vmapi/hf/types.h"

/** The number of bits in each element of the interrupt bitfields. */
#define INTERRUPT_REGISTER_BITS 32

enum vcpu_state {
	/** The vcpu is switched off. */
	vcpu_state_off,

	/** The vcpu is ready to be run. */
	vcpu_state_ready,

	/** The vcpu is currently running. */
	vcpu_state_running,

	/** The vcpu is waiting for a message. */
	vcpu_state_blocked_mailbox,

	/** The vcpu is waiting for an interrupt. */
	vcpu_state_blocked_interrupt,

	/** The vcpu has aborted. */
	vcpu_state_aborted,
};

struct interrupts {
	/** Bitfield keeping track of which interrupts are enabled. */
	uint32_t interrupt_enabled[HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS];
	/** Bitfield keeping track of which interrupts are pending. */
	uint32_t interrupt_pending[HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS];
	/**
	 * The number of interrupts which are currently both enabled and
	 * pending. i.e. the number of bits set in interrupt_enable &
	 * interrupt_pending.
	 */
	uint32_t enabled_and_pending_count;
};

struct retval_state {
	uintptr_t value;
	bool force;
};

struct vcpu {
	struct spinlock lock;
	enum vcpu_state state;
	struct cpu *cpu;
	struct vm *vm;
	struct vcpu *mailbox_next;
	struct arch_regs regs;
	struct interrupts interrupts;

	/*
	 * The following field is used to force a return value to be set the
	 * next time a vCPU belonging to a secondary VM runs. For primary VMs,
	 * 'regs' can be set directly.
	 */
	struct retval_state retval;

	/*
	 * Determine whether the 'regs' field is available for use. This is set
	 * to false when a vCPU is about to run on a physical CPU, and is set
	 * back to true when it is descheduled.
	 */
	bool regs_available;
};

/* TODO: Update alignment such that cpus are in different cache lines. */
struct cpu {
	/** CPU identifier. Doesn't have to be contiguous. */
	size_t id;

	/** Pointer to bottom of the stack. */
	void *stack_bottom;

	/**
	 * Enabling/disabling irqs are counted per-cpu. They are enabled when
	 * the count is zero, and disabled when it's non-zero.
	 */
	uint32_t irq_disable_count;

	/** See api.c for the partial ordering on locks. */
	struct spinlock lock;

	/** Determines whether or not the cpu is currently on. */
	bool is_on;
};

void cpu_module_init(void);

void cpu_init(struct cpu *c);
size_t cpu_index(struct cpu *c);
void cpu_irq_enable(struct cpu *c);
void cpu_irq_disable(struct cpu *c);
bool cpu_on(struct cpu *c, ipaddr_t entry, uintreg_t arg);
void cpu_off(struct cpu *c);
struct cpu *cpu_find(size_t id);

void vcpu_init(struct vcpu *vcpu, struct vm *vm);
void vcpu_on(struct vcpu *vcpu);
void vcpu_off(struct vcpu *vcpu);
size_t vcpu_index(const struct vcpu *vcpu);
