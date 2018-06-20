#ifndef _TIMER_H
#define _TIMER_H

#include <stdbool.h>

void timer_init(void);
void timer_init_percpu(void);
void timer_set(uint64_t time, bool (*cb)(void *), void *context);

#endif  /* _TIMER_H */
