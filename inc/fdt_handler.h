#ifndef _FDT_HANDLER_H
#define _FDT_HANDLER_H

#include "boot_params.h"
#include "fdt.h"
#include "mm.h"

bool fdt_get_boot_params(paddr_t fdt_addr, struct boot_params *p);
bool fdt_patch(paddr_t fdt_addr, struct boot_params_update *p);

#endif /* _FDT_HANDLER_H */
