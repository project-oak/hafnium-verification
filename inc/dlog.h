#ifndef _DLOG_H
#define _DLOG_H

#include <stdarg.h>

#if DEBUG
void dlog(const char *fmt, ...);
void vdlog(const char *fmt, va_list args);
#else
#define dlog(...)
#define vdlog(fmt, args)
#endif

#endif /* _DLOG_H */
