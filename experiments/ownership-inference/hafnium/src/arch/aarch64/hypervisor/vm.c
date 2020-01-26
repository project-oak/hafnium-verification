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

#include "hf/arch/vm.h"

#include "hypervisor/feature_id.h"

void arch_vm_features_set(struct vm *vm)
{
	/* Features to trap for all VMs. */

	/*
	 * It is not safe to enable this yet, in part, because the feature's
	 * registers are not context switched in Hafnium.
	 */
	vm->arch.trapped_features |= HF_FEATURE_LOR;

	vm->arch.trapped_features |= HF_FEATURE_SPE;

	vm->arch.trapped_features |= HF_FEATURE_TRACE;

	vm->arch.trapped_features |= HF_FEATURE_DEBUG;

	if (vm->id != HF_PRIMARY_VM_ID) {
		/* Features to trap only for the secondary VMs. */

		vm->arch.trapped_features |= HF_FEATURE_PERFMON;

		/*
		 * TODO(b/132395845): Access to RAS registers is not trapped at
		 * the moment for the primary VM, only for the secondaries. RAS
		 * register access isn't needed now, but it might be
		 * required for debugging. When Hafnium introduces debug vs
		 * release builds, trap accesses for primary VMs in release
		 * builds, but do not trap them in debug builds.
		 */
		vm->arch.trapped_features |= HF_FEATURE_RAS;

		/*
		 * The PAuth mechanism holds state in the key registers. Only
		 * the primary VM is allowed to use the PAuth functionality for
		 * now. This prevents Hafnium from having to save/restore the
		 * key register on a VM switch.
		 */
		vm->arch.trapped_features |= HF_FEATURE_PAUTH;
	}
}
