#ifndef _LIST_H
#define _LIST_H

#include <stdbool.h>

struct list_entry {
	struct list_entry *next;
	struct list_entry *prev;
};

#define LIST_INIT(l) {.next = &l, .prev = &l}
#define LIST_ELEM(ptr, type, field) \
	((type*)(char*)ptr - offsetof(type, field))

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
}

#endif  /* _LIST_H */
