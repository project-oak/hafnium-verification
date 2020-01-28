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

#include "hf/abort.h"

/**
 * Causes execution to halt and prevent progress of the current and less
 * privileged software components. This should be triggered when a
 * non-recoverable event is identified which leaves the system in an
 * inconsistent state.
 *
 * TODO: Should this also reset the system?
 */
noreturn void abort(void)
{
	/* TODO: Block all CPUs. */
	for (;;) {
		/* Prevent loop being optimized away. */
		__asm__ volatile("nop");
	}
}
