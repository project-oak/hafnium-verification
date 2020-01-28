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

.global vm_cpu_entry
vm_cpu_entry:
	/* Disable trapping floating point access in EL1. */
	mov x1, #(0x3 << 20)
	msr cpacr_el1, x1
	isb

	/* Initialise stack from the cpu_start_state struct. */
	ldr x1, [x0]
	mov sp, x1

	/* Load entry function pointer and its argument. */
	ldr x1, [x0, 8]
	ldr x0, [x0, 16]

	/* Branch to entry function. */
	blr x1

	/* Entry function should not return, but if it does, spin. */
	b .
