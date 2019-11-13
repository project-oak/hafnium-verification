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

#include <stdatomic.h>

struct spinlock {
	atomic_flag v;
};

#define SPINLOCK_INIT                 \
	{                             \
		.v = ATOMIC_FLAG_INIT \
	}

void sl_init(struct spinlock *l);
void sl_lock(struct spinlock *l);
void sl_unlock(struct spinlock *l);
