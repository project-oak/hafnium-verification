#ifndef _FDT_HANDLER_H
#define _FDT_HANDLER_H

#include "boot_params.h"
#include "fdt.h"

bool fdt_get_boot_params(struct fdt_header *fdt, struct boot_params *p);
bool fdt_patch(struct fdt_header *fdt, struct boot_params_update *p);

#endif /* _FDT_HANDLER_H */
