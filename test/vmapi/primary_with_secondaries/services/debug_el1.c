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

#include "../debug_el1.h"

#include "hf/dlog.h"

TEST_SERVICE(debug_el1_secondary_mdccint_el1)
{
	EXPECT_GT(hf_vm_get_id(), HF_PRIMARY_VM_ID);
	TRY_READ(MDCCINT_EL1);
	FAIL("Reading debug EL1 register in secondary VM didn't trap.");
}

TEST_SERVICE(debug_el1_secondary_dbgbcr0_el1)
{
	EXPECT_GT(hf_vm_get_id(), HF_PRIMARY_VM_ID);
	TRY_READ(DBGBCR0_EL1);
	FAIL("Reading debug EL1 register in secondary VM didn't trap.");
}

TEST_SERVICE(debug_el1_secondary_dbgbvr0_el1)
{
	EXPECT_GT(hf_vm_get_id(), HF_PRIMARY_VM_ID);
	TRY_READ(DBGBVR0_EL1);
	FAIL("Reading debug EL1 register in secondary VM didn't trap.");
}

TEST_SERVICE(debug_el1_secondary_dbgwcr0_el1)
{
	EXPECT_GT(hf_vm_get_id(), HF_PRIMARY_VM_ID);
	TRY_READ(DBGWCR0_EL1);
	FAIL("Reading debug EL1 register in secondary VM didn't trap.");
}

TEST_SERVICE(debug_el1_secondary_dbgwvr0_el1)
{
	EXPECT_GT(hf_vm_get_id(), HF_PRIMARY_VM_ID);
	TRY_READ(DBGWVR0_EL1);
	FAIL("Reading debug EL1 register in secondary VM didn't trap.");
}
