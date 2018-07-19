#ifndef _DLOG_H
#define _DLOG_H

#if DEBUG
void dlog(const char *fmt, ...);
#else
#define dlog(...)
#endif

void dlog_init(void (*pchar)(char));

#endif /* _DLOG_H */
