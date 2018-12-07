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

.section .text.vector_table_el1, "ax"
.global vector_table_el1
.balign 0x800
vector_table_el1:
sync_cur_sp0:
	b .

.balign 0x80
irq_cur_sp0:
	b irq_current
	eret

.balign 0x80
fiq_cur_sp0:
	b .

.balign 0x80
serr_cur_sp0:
	b .

.balign 0x80
sync_cur_spx:
	mrs x0, esr_el1
	mrs x1, elr_el1
	b sync_current_exception

.balign 0x80
irq_cur_spx:
	b irq_current
	eret

.balign 0x80
fiq_cur_spx:
	b .

.balign 0x80
serr_cur_spx:
	b .

.balign 0x80
sync_lower_64:
	b .

.balign 0x80
irq_lower_64:
	b .

.balign 0x80
fiq_lower_64:
	b .

.balign 0x80
serr_lower_64:
	b .

.balign 0x80
sync_lower_32:
	b .

.balign 0x80
irq_lower_32:
	b .

.balign 0x80
fiq_lower_32:
	b .

.balign 0x80
serr_lower_32:
	b .
