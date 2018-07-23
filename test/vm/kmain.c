#include <stddef.h>
#include <stdint.h>

#include "dlog.h"

uint8_t kstack[4096] __attribute__((aligned(4096)));

void kmain(void)
{
	dlog("Here we go!\n");
	while (1) {
		/* Do nothing */
	}
}
