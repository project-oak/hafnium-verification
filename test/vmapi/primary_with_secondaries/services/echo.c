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

#include "hf/arch/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

TEST_SERVICE(echo)
{
	/* Loop, echo messages back to the sender. */
	for (;;) {
		struct hf_mailbox_receive_return res = hf_mailbox_receive(true);
		memcpy(SERVICE_SEND_BUFFER(), SERVICE_RECV_BUFFER(), res.size);
		hf_mailbox_clear();
		hf_mailbox_send(res.vm_id, res.size, false);
	}
}
