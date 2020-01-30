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

#include "vmapi/hf/call.h"

#include "../msr.h"
#include "test/hftest.h"

/**
 * Test that encoding a system register using the implementation defined syntax
 * maps to the same register defined by name.
 */
TEST(arch_features, read_write_msr_impdef)
{
	uintreg_t value = 0xa;
	write_msr(S3_3_C9_C13_0, value);
	EXPECT_EQ(read_msr(S3_3_C9_C13_0), value);
	EXPECT_EQ(read_msr(PMCCNTR_EL0), value);
}
