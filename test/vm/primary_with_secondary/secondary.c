#include <stdalign.h>
#include <stdint.h>

#include "vmapi/hf/call.h"

#include "../hftest.h"

alignas(4096) uint8_t kstack[4096];

void kmain(void)
{
	for (;;) {
		/* Do nothing. */
	}
}
