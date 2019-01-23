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

#include "hf/mm.h"
#include "hf/std.h"

#include "vmapi/hf/call.h"

#include "hftest.h"

TEST_SERVICE(data_abort)
{
	/* Not using NULL so static analysis doesn't complain. */
	int *p = (int *)1;
	*p = 12;
}

TEST_SERVICE(instruction_abort)
{
	/* Not using NULL so static analysis doesn't complain. */
	int (*f)(void) = (int (*)(void))4;
	f();
}
