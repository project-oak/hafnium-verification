#include "cpu.h"
#include "decl_offsets.h"

void dummy(void)
{
	DECL(CPU_CURRENT, struct cpu, current);
	DECL(CPU_STACK_BOTTOM, struct cpu, stack_bottom);
	DECL(VCPU_REGS, struct vcpu, regs);
	DECL(VCPU_LAZY, struct vcpu, regs.lazy);
}
