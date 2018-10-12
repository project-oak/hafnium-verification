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

#include "hf/boot_params.h"
#include "hf/fdt_handler.h"

/* This is set by entry.S. */
uintpaddr_t fdt_addr;

/*
 * The following are declared weak so that they can overwritten by platform code
 * if desired.
 */
#pragma weak plat_get_boot_params
bool plat_get_boot_params(struct boot_params *p)
{
	return fdt_get_boot_params(pa_init(fdt_addr), p);
}

#pragma weak plat_update_boot_params
bool plat_update_boot_params(struct boot_params_update *p)
{
	return fdt_patch(pa_init(fdt_addr), p);
}
