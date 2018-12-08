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

.section .init.image_entry, "ax"
.global image_entry
image_entry:
	/* Prepare the stack. */
	adr x30, kstack + 4096
	mov sp, x30

	/* Call into C code. */
	bl kmain

	/* If the VM returns, shutdown the system. */
	bl shutdown

	/* Loop forever waiting for interrupts. */
0:	wfi
	b 0b
