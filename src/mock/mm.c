#include "hf/mm.h"

#include "hf/dlog.h"

bool mm_init(void)
{
	return true;
}

bool mm_cpu_init(void)
{
	return true;
}

void mm_defrag(void)
{
}

void *mm_identity_map(paddr_t begin, paddr_t end, int mode)
{
	(void)end;
	(void)mode;
	return ptr_from_va(va_from_pa(begin));
}

bool mm_unmap(paddr_t begin, paddr_t end, int mode)
{
	(void)begin;
	(void)end;
	(void)mode;
	return false;
}

bool mm_vm_translate(struct mm_ptable *t, ipaddr_t ipa, paddr_t *pa)
{
	(void)t;
	(void)ipa;
	(void)pa;
	return false;
}

bool mm_ptable_init(struct mm_ptable *t, int mode)
{
	(void)t;
	(void)mode;
	return true;
}

bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
			int mode, ipaddr_t *ipa)
{
	(void)t;
	(void)end;
	(void)mode;
	*ipa = ipa_from_pa(begin);

	return true;
}

bool mm_vm_identity_map_page(struct mm_ptable *t, paddr_t begin, int mode,
			     ipaddr_t *ipa)
{
	(void)t;
	(void)mode;
	*ipa = ipa_from_pa(begin);

	return true;
}
