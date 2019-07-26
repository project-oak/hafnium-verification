#include "hf/cpu.h"
#include "hf/mm.h"

extern char callstacks[MAX_CPUS][PAGE_SIZE];

struct cpu cpus = {
    .is_on = 1,
    .stack_bottom = &callstacks[0][PAGE_SIZE],
}; 
