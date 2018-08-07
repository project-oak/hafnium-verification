#include <stdint.h>

#include "../hf_test.h"
#include "vmapi/hf/call.h"

uint8_t kstack[4096] __attribute__((aligned(4096)));

void kmain(void)
{
	for (;;) {
		/* Do nothing. */
	}
}
