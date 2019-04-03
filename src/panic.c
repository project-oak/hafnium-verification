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

#include "hf/panic.h"

#include <stdarg.h>

#include "hf/dlog.h"

/**
 * Blocks the hypervisor.
 *
 * TODO: Determine if we want to omit strings on non-debug builds.
 */
noreturn void panic(const char *fmt, ...)
{
	va_list args;

	/* TODO: Block all CPUs. */

	dlog("Panic: ");

	va_start(args, fmt);
	vdlog(fmt, args);
	va_end(args);

	dlog("\n");

	for (;;) {
	}
}
