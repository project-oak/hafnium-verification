#include "alloc.h"

#include "dlog.h"
#include "spinlock.h"

static size_t alloc_base;
static size_t alloc_limit;
static struct spinlock alloc_lock = SPINLOCK_INIT;

/**
 * Initializes the allocator.
 */
void halloc_init(size_t base, size_t size)
{
	alloc_base = base;
	alloc_limit = base + size;
}

/**
 * Allocates the requested amount of memory. Returns NULL when there isn't
 * enough free memory.
 */
void *halloc(size_t size)
{
	return halloc_aligned(size, 2 * sizeof(size_t));
}

/**
 * Frees the provided memory.
 *
 * Currently unimplemented.
 */
void hfree(void *ptr)
{
	dlog("Attempted to free pointer %p\n", ptr);
}

/**
 * Allocates the requested amount of memory, with the requested alignment.
 *
 * Alignment must be a power of two. Returns NULL when there isn't enough free
 * memory.
 */
void *halloc_aligned(size_t size, size_t align)
{
	void *ret;

	sl_lock(&alloc_lock);
	ret = halloc_aligned_nosync(size, align);
	sl_unlock(&alloc_lock);

	return ret;
}

/**
 * Allocates the requested amount of memory, with the requested alignment, but
 * no synchronisation with other CPUs. The caller is responsible for serialising
 * all such calls.
 *
 * Alignment must be a power of two. Returns NULL when there isn't enough free
 * memory.
 */
void *halloc_aligned_nosync(size_t size, size_t align)
{
	size_t begin;
	size_t end;

	begin = (alloc_base + align - 1) & ~(align - 1);
	end = begin + size;

	/* Check for overflows, and that there is enough free mem. */
	if (end > begin && begin >= alloc_base && end <= alloc_limit) {
		alloc_base = end;
	} else {
		begin = 0;
	}

	return (void *)begin;
}
