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

#pragma once

#include <stdbool.h>
#include <stddef.h>

struct list_entry {
	struct list_entry *next;
	struct list_entry *prev;
};

#define LIST_INIT(l)                   \
	{                              \
		.next = &l, .prev = &l \
	}
#define CONTAINER_OF(ptr, type, field) \
	((type *)((char *)ptr - offsetof(type, field)))

static inline void list_init(struct list_entry *e)
{
	e->next = e;
	e->prev = e;
}

static inline void list_append(struct list_entry *l, struct list_entry *e)
{
	e->next = l;
	e->prev = l->prev;

	e->next->prev = e;
	e->prev->next = e;
}

static inline void list_prepend(struct list_entry *l, struct list_entry *e)
{
	e->next = l->next;
	e->prev = l;

	e->next->prev = e;
	e->prev->next = e;
}

static inline bool list_empty(struct list_entry *l)
{
	return l->next == l;
}

static inline void list_remove(struct list_entry *e)
{
	e->prev->next = e->next;
	e->next->prev = e->prev;
	list_init(e);
}
