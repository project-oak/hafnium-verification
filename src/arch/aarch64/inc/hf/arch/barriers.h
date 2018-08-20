#pragma once

static inline void dmb(void)
{
	__asm__ volatile("dmb sy");
}

static inline void dsb(void)
{
	__asm__ volatile("dsb sy");
}

static inline void isb(void)
{
	__asm__ volatile("isb");
}
