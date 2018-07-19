#include "dlog.h"

#include <stdbool.h>
#include <stddef.h>

#include "arch.h"
#include "spinlock.h"
#include "std.h"

/* Keep macro alignment */
/* clang-format off */

#define FLAG_SPACE 0x01
#define FLAG_ZERO  0x02
#define FLAG_MINUS 0x04
#define FLAG_PLUS  0x08
#define FLAG_ALT   0x10
#define FLAG_UPPER 0x20
#define FLAG_NEG   0x40

/* clang-format on */

/**
 * Prints a raw string to the debug log and returns its length.
 */
static size_t print_raw_string(const char *str)
{
	const char *c = str;
	while (*c != '\0') {
		arch_putchar(*c++);
	}
	return c - str;
}

/**
 * Prints a formatted string to the debug log. The format includes a minimum
 * width, the fill character, and flags (whether to align to left or right).
 *
 * str is the full string, while suffix is a pointer within str that indicates
 * where the suffix begins. This is used when printing right-aligned numbers
 * with a zero fill; for example, -10 with width 4 should be padded to -010,
 * so suffix would point to index one of the "-10" string .
 */
static void print_string(const char *str, const char *suffix, size_t width,
			 int flags, char fill)
{
	size_t len = suffix - str;

	/* Print the string up to the beginning of the suffix. */
	while (str != suffix) {
		arch_putchar(*str++);
	}

	if (flags & FLAG_MINUS) {
		/* Left-aligned. Print suffix, then print padding if needed. */
		len += print_raw_string(suffix);
		while (len < width) {
			arch_putchar(' ');
			len++;
		}
		return;
	}

	/* Fill until we reach the desired length. */
	len += strlen(suffix);
	while (len < width) {
		arch_putchar(fill);
		len++;
	}

	/* Now print the rest of the string. */
	print_raw_string(suffix);
}

/**
 * Prints a number to the debug log. The caller specifies the base, its minimum
 * width and printf-style flags.
 */
static void print_num(size_t v, size_t base, size_t width, int flags)
{
	static const char *digits_lower = "0123456789abcdefx";
	static const char *digits_upper = "0123456789ABCDEFX";
	const char *d = (flags & FLAG_UPPER) ? digits_upper : digits_lower;
	char buf[51];
	char *ptr = buf + sizeof(buf) - 1;
	char *num;
	*ptr = '\0';
	do {
		--ptr;
		*ptr = d[v % base];
		v /= base;
	} while (v);

	/* Num stores where the actual number begins. */
	num = ptr;

	/* Add prefix if requested. */
	if (flags & FLAG_ALT) {
		switch (base) {
		case 16:
			ptr -= 2;
			ptr[0] = '0';
			ptr[1] = d[16];
			break;

		case 8:
			ptr--;
			*ptr = '0';
			break;
		}
	}

	/* Add sign if requested. */
	if (flags & FLAG_NEG) {
		*--ptr = '-';
	} else if (flags & FLAG_PLUS) {
		*--ptr = '+';
	} else if (flags & FLAG_SPACE) {
		*--ptr = ' ';
	}
	if (flags & FLAG_ZERO) {
		print_string(ptr, num, width, flags, '0');
	} else {
		print_string(ptr, ptr, width, flags, ' ');
	}
}

/**
 * Parses the optional flags field of a printf-style format. It returns the spot
 * on the string where a non-flag character was found.
 */
static const char *parse_flags(const char *p, int *flags)
{
	for (;;) {
		switch (*p) {
		case ' ':
			*flags |= FLAG_SPACE;
			break;

		case '0':
			*flags |= FLAG_ZERO;
			break;

		case '-':
			*flags |= FLAG_MINUS;
			break;

		case '+':
			*flags |= FLAG_PLUS;

		case '#':
			*flags |= FLAG_ALT;
			break;

		default:
			return p;
		}
		p++;
	}
}

/**
 * Same as "dlog", except that arguments are passed as a va_list.
 */
void vdlog(const char *fmt, va_list args)
{
	static struct spinlock sl = SPINLOCK_INIT;
	const char *p;
	size_t w;
	int flags;
	char buf[2];

	sl_lock(&sl);

	for (p = fmt; *p; p++) {
		switch (*p) {
		default:
			arch_putchar(*p);
			break;

		case '%':
			/* Read optional flags. */
			flags = 0;
			p = parse_flags(p + 1, &flags) - 1;

			/* Read the minimum width, if one is specified. */
			w = 0;
			while (p[1] >= '0' && p[1] <= '9') {
				w = (w * 10) + (p[1] - '0');
				p++;
			}

			/* Read minimum width from arguments. */
			if (w == 0 && p[1] == '*') {
				int v = va_arg(args, int);
				if (v >= 0) {
					w = v;
				} else {
					w = -v;
					flags |= FLAG_MINUS;
				}
				p++;
			}

			/* Handle the format specifier. */
			switch (p[1]) {
			case 's': {
				char *str = va_arg(args, char *);
				print_string(str, str, w, flags, ' ');
				p++;
			} break;

			case 'd':
			case 'i': {
				int v = va_arg(args, int);
				if (v < 0) {
					flags |= FLAG_NEG;
					v = -v;
				}

				print_num((size_t)v, 10, w, flags);
				p++;
			} break;

			case 'X':
				flags |= FLAG_UPPER;
				print_num(va_arg(args, size_t), 16, w, flags);
				break;

			case 'p':
				print_num(va_arg(args, size_t), 16,
					  sizeof(size_t) * 2, FLAG_ZERO);
				p++;
				break;

			case 'x':
				print_num(va_arg(args, size_t), 16, w, flags);
				p++;
				break;

			case 'u':
				print_num(va_arg(args, size_t), 10, w, flags);
				p++;
				break;

			case 'o':
				print_num(va_arg(args, size_t), 8, w, flags);
				p++;
				break;

			case 'c':
				buf[1] = 0;
				buf[0] = va_arg(args, int);
				print_string(buf, buf, w, flags, ' ');
				p++;
				break;

			case '%':
				break;

			default:
				arch_putchar('%');
			}

			break;
		}
	}

	sl_unlock(&sl);
}

/**
 * Prints the given format string to the debug log.
 */
void dlog(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	vdlog(fmt, args);
	va_end(args);
}
