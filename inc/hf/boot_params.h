#ifndef _BOOT_PARAMS_H
#define _BOOT_PARAMS_H

#include <stdbool.h>

#include "hf/mm.h"

struct boot_params {
	paddr_t mem_begin;
	paddr_t mem_end;
	paddr_t initrd_begin;
	paddr_t initrd_end;
	size_t kernel_arg;
};

struct boot_params_update {
	paddr_t reserved_begin;
	paddr_t reserved_end;
	paddr_t initrd_begin;
	paddr_t initrd_end;
};

bool plat_get_boot_params(struct boot_params *p);
bool plat_update_boot_params(struct boot_params_update *p);

#endif /* _BOOT_PARAMS_H */
