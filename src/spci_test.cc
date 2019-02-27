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

extern "C" {
#include "vmapi/hf/spci.h"
}

#include <gmock/gmock.h>

namespace
{
using ::testing::Eq;

/**
 * Ensure that spci_message_init is correctly setting the expected fields in the
 * SPCI common message header.
 */
TEST(spci, spci_message_init)
{
	spci_message header;
	spci_message compare_header = {
		.flags = SPCI_MESSAGE_IMPDEF_MASK,
		.length = 1,
		.target_vm_id = 2,
		.source_vm_id = 3,
	};

	memset(&header, 0xff, sizeof(header));
	spci_message_init(&header, 1, 2, 3);

	EXPECT_THAT(memcmp(&header, &compare_header, sizeof(header)), 0);
}
} /* namespace */
