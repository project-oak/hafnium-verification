#pragma once

#include <stddef.h>

#define read_msr(name)                                        \
	__extension__({                                       \
		size_t __v;                                   \
		__asm volatile("mrs %0, " #name : "=r"(__v)); \
		__v;                                          \
	})

#define write_msr(name, value)                           \
	do {                                             \
		__asm volatile("msr " #name ", %x0"      \
			       :                         \
			       : "rZ"((size_t)(value))); \
	} while (0)
