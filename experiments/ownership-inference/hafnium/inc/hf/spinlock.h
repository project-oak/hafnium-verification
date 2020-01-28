/*
 * Copyright 2018 The Hafnium Authors.
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

/*
 * Includes the arch-specific definition of 'struct spinlock' and
 * implementations of:
 *  - SPINLOCK_INIT
 *  - sl_lock()
 *  - sl_unlock()
 */
#include "hf/arch/spinlock.h"

static inline void sl_init(struct spinlock *l)
{
	*l = SPINLOCK_INIT;
}

/**
 * Locks both locks, enforcing the lowest address first ordering for locks of
 * the same kind.
 */
static inline void sl_lock_both(struct spinlock *a, struct spinlock *b)
{
	if (a < b) {
		sl_lock(a);
		sl_lock(b);
	} else {
		sl_lock(b);
		sl_lock(a);
	}
}
