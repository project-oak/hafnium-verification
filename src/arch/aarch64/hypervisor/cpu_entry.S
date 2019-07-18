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

#include "offsets.h"

.section .text.cpu_entry, "ax"
.global cpu_entry
cpu_entry:
	/* Disable interrupts. */
	msr DAIFSet, #0xf

	/* Use SPx (instead of SP0). */
	msr spsel, #1

	/* Prepare the stack. */
	ldr x30, [x0, #CPU_STACK_BOTTOM]
	mov sp, x30

	/* Configure exception handlers. */
	adrp x30, vector_table_el2
	add x30, x30, :lo12:vector_table_el2
	msr vbar_el2, x30

	/* Call into C code, x0 holds the cpu pointer. */
	bl cpu_main

	/* Run the vcpu returned by cpu_main. */
	bl vcpu_restore_all_and_run

	/* Loop forever waiting for interrupts. */
0:	wfi
	b 0b
