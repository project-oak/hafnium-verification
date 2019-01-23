/*
 * Copyright 2019 Google LLC
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

#include "hf/arch/cpu.h"
#include "hf/arch/vm/interrupts_gicv3.h"

#include "hf/dlog.h"

#include "vmapi/hf/call.h"

#include "common.h"
#include "hftest.h"

/*
 * Secondary VM that loops forever after receiving a message.
 */

TEST_SERVICE(busy)
{
	dlog("Secondary waiting for message...\n");
	(void)mailbox_receive_retry();
	hf_mailbox_clear();
	dlog("Secondary received message, looping forever.\n");
	for (;;) {
	}
}
