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

#include <stdint.h>
#include <stdnoreturn.h>

#include "hf/panic.h"

/**
 * This is the value that is used as the stack canary. It is written to the top
 * of the stack when entering a function and compared against the stack when
 * exiting a function. If there is a mismatch, a failure is triggered.
 *
 * As the value must be the same at the beginning and end of the function, this
 * is a global variable and there are multiple CPUs executing concurrently, this
 * value cannot change after being initialized.
 *
 * TODO: initialize to a random value at boot.
 */
uint64_t __attribute__((used)) __stack_chk_guard = 0x72afaf72bad0feed;

/**
 * Called when the stack canary is invalid. The stack can no longer be trusted
 * so this function must not return.
 */
noreturn void __stack_chk_fail(void)
{
	panic("stack corruption");
}
