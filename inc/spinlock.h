#ifndef _SPINLOCK_H
#define _SPINLOCK_H

#include <stdatomic.h>

struct spinlock {
	atomic_flag v;
};

#define SPINLOCK_INIT {.v = ATOMIC_FLAG_INIT}

static inline void sl_init(struct spinlock *l)
{
	*l = (struct spinlock)SPINLOCK_INIT;
}

static inline void sl_lock(struct spinlock *l)
{
	while (atomic_flag_test_and_set_explicit(&l->v, memory_order_acquire));
}

static inline void sl_unlock(struct spinlock *l)
{
	atomic_flag_clear_explicit(&l->v, memory_order_release);
}

#endif  /* _SPINLOCK_H */
