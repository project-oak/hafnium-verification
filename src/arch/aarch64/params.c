#include "hf/boot_params.h"
#include "hf/fdt_handler.h"

/* This is set by entry.S. */
uintpaddr_t fdt_addr;

/*
 * The following are declared weak so that they can overwritten by platform code
 * if desired.
 */
#pragma weak plat_get_boot_params
bool plat_get_boot_params(struct boot_params *p)
{
	return fdt_get_boot_params(pa_init(fdt_addr), p);
}

#pragma weak plat_update_boot_params
bool plat_update_boot_params(struct boot_params_update *p)
{
	return fdt_patch(pa_init(fdt_addr), p);
}
