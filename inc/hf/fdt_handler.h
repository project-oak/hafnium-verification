#pragma once

#include "hf/boot_params.h"
#include "hf/fdt.h"
#include "hf/mm.h"

bool fdt_get_boot_params(paddr_t fdt_addr, struct boot_params *p);
bool fdt_patch(paddr_t fdt_addr, struct boot_params_update *p);
