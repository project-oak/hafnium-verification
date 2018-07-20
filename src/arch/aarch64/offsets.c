#ifndef GEN_OFFSETS
#include "offsets.h"
#endif /* GEN_OFFSETS */

#include "cpu.h"
#include "decl_offsets.h"

DECL(CPU_CURRENT, struct cpu, current);
DECL(CPU_STACK_BOTTOM, struct cpu, stack_bottom);
DECL(VCPU_REGS, struct vcpu, regs);
DECL(VCPU_LAZY, struct vcpu, regs.lazy);
