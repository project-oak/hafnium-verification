#ifndef _DECL_OFFSETS_H
#define _DECL_OFFSETS_H

#define DECL(name, type, field) \
	__asm("DEFINE_OFFSET " #name " %0" : : "n" (offsetof(type, field)))

#define DECL_SIZE(name, type) \
	__asm("DEFINE_OFFSET " #name " %0" : : "n" (sizeof(type)))

#endif  /* _DECL_OFFSETS_H */
