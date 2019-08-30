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

.section .text.smc_internal, "ax"
.global smc_internal

smc_internal:
	str x8, [sp, #-16] ! /* AArch64 stack pointer alignment is 16 bytes */
	smc #0
	ldr x8, [sp], #16
	stp x0, x1, [x8]
	stp x2, x3, [x8, #16]
	ret
