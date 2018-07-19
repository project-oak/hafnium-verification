#ifndef _DECL_OFFSETS_H
#define _DECL_OFFSETS_H

#define DECL(name, type, field) \
    const size_t DEFINE_OFFSET__##name = offsetof(type, field)

#define DECL_SIZE(name, type) \
    const size_t DEFINE_OFFSET__name = sizeof(type)

#endif  /* _DECL_OFFSETS_H */
