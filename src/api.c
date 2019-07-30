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

#include "hf/api.h"

#include "hf/arch/cpu.h"
#include "hf/arch/timer.h"

#include "hf/check.h"
#include "hf/dlog.h"
#include "hf/mm.h"
#include "hf/plat/console.h"
#include "hf/spci_internal.h"
#include "hf/spinlock.h"
#include "hf/static_assert.h"
#include "hf/std.h"
#include "hf/vm.h"

#include "vmapi/hf/call.h"
#include "vmapi/hf/spci.h"

/*
 * To eliminate the risk of deadlocks, we define a partial order for the
 * acquisition of locks held concurrently by the same physical CPU. Our current
 * ordering requirements are as follows:
 *
 * vm::lock -> vcpu::lock -> mm_stage1_lock -> dlog sl
 *
 * Locks of the same kind require the lock of lowest address to be locked first,
 * see `sl_lock_both()`.
 */

/**
 * Prepares the vcpu to run by updating its state and fetching whether a return
 * value needs to be forced onto the vCPU.
 */
bool api_vcpu_prepare_run(const struct vcpu *current, struct vcpu *vcpu,
				 struct hf_vcpu_run_return *run_ret)
{
	bool need_vm_lock;
	bool ret;

	/*
	 * Wait until the registers become available. All locks must be released
	 * between iterations of this loop to avoid potential deadlocks if, on
	 * any path, a lock needs to be taken after taking the decision to
	 * switch context but before the registers have been saved.
	 *
	 * The VM lock is not needed in the common case so it must only be taken
	 * when it is going to be needed. This ensures there are no inter-vCPU
	 * dependencies in the common run case meaning the sensitive context
	 * switch performance is consistent.
	 */
	for (;;) {
		sl_lock(&vcpu->lock);

		/* The VM needs to be locked to deliver mailbox messages. */
		need_vm_lock = vcpu->state == VCPU_STATE_BLOCKED_MAILBOX;
		if (need_vm_lock) {
			sl_unlock(&vcpu->lock);
			sl_lock(&vcpu->vm->lock);
			sl_lock(&vcpu->lock);
		}

		if (vcpu->regs_available) {
			break;
		}

		if (vcpu->state == VCPU_STATE_RUNNING) {
			/*
			 * vCPU is running on another pCPU.
			 *
			 * It's ok not to return the sleep duration here because
			 * the other physical CPU that is currently running this
			 * vCPU will return the sleep duration if needed. The
			 * default return value is
			 * HF_VCPU_RUN_WAIT_FOR_INTERRUPT, so no need to set it
			 * explicitly.
			 */
			ret = false;
			goto out;
		}

		sl_unlock(&vcpu->lock);
		if (need_vm_lock) {
			sl_unlock(&vcpu->vm->lock);
		}
	}

	if (atomic_load_explicit(&vcpu->vm->aborting, memory_order_relaxed)) {
		if (vcpu->state != VCPU_STATE_ABORTED) {
			dlog("Aborting VM %u vCPU %u\n", vcpu->vm->id,
			     vcpu_index(vcpu));
			vcpu->state = VCPU_STATE_ABORTED;
		}
		ret = false;
		goto out;
	}

	switch (vcpu->state) {
	case VCPU_STATE_RUNNING:
	case VCPU_STATE_OFF:
	case VCPU_STATE_ABORTED:
		ret = false;
		goto out;

	case VCPU_STATE_BLOCKED_MAILBOX:
		/*
		 * A pending message allows the vCPU to run so the message can
		 * be delivered directly.
		 */
		if (vcpu->vm->mailbox.state == MAILBOX_STATE_RECEIVED) {
			arch_regs_set_retval(&vcpu->regs, SPCI_SUCCESS);
			vcpu->vm->mailbox.state = MAILBOX_STATE_READ;
			break;
		}
		/* Fall through. */
	case VCPU_STATE_BLOCKED_INTERRUPT:
		/* Allow virtual interrupts to be delivered. */
		if (vcpu->interrupts.enabled_and_pending_count > 0) {
			break;
		}

		/* The timer expired so allow the interrupt to be delivered. */
		if (arch_timer_pending(&vcpu->regs)) {
			break;
		}

		/*
		 * The vCPU is not ready to run, return the appropriate code to
		 * the primary which called vcpu_run.
		 */
		if (arch_timer_enabled(&vcpu->regs)) {
			run_ret->code =
				vcpu->state == VCPU_STATE_BLOCKED_MAILBOX
					? HF_VCPU_RUN_WAIT_FOR_MESSAGE
					: HF_VCPU_RUN_WAIT_FOR_INTERRUPT;
			run_ret->sleep.ns =
				arch_timer_remaining_ns(&vcpu->regs);
		}

		ret = false;
		goto out;

	case VCPU_STATE_READY:
		break;
	}

	/* It has been decided that the vCPU should be run. */
	vcpu->cpu = current->cpu;
	vcpu->state = VCPU_STATE_RUNNING;

	/*
	 * Mark the registers as unavailable now that we're about to reflect
	 * them onto the real registers. This will also prevent another physical
	 * CPU from trying to read these registers.
	 */
	vcpu->regs_available = false;

	ret = true;

out:
	sl_unlock(&vcpu->lock);
	if (need_vm_lock) {
		sl_unlock(&vcpu->vm->lock);
	}

	return ret;
}
