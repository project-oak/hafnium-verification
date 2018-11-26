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

#include "offsets.h"

.section .init.image_entry, "ax"
.global image_entry
image_entry:
	/* Interpret the registers passed from the loader. */
	bl plat_entry

	/* Get pointer to first cpu. */
	adrp x0, cpus
	add x0, x0, :lo12:cpus

	/* Set the ID of this cpu from the affinity bits of mpidr. */
	mrs x30, mpidr_el1
	ubfx x29, x30, 0, 24
	ubfx x30, x30, 32, 8
	orr x30, x29, x30
	str x30, [x0, CPU_ID]

	b cpu_entry
