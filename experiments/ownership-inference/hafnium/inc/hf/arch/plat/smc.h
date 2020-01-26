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

#pragma once

#include "vmapi/hf/spci.h"

/**
 * Called after an SMC has been forwarded. `args` contains the arguments passed
 * to the SMC and `ret` contains the return values that will be set in the vCPU
 * registers after this call returns.
 */
void plat_smc_post_forward(struct spci_value args, struct spci_value *ret);
