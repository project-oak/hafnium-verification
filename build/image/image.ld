/*
 * Code will start running at this symbol which is places at the start of the
 * image.
 */
ENTRY(entry)

/*
 * The following would be useful to check that .init code is not called back
 * into once it has completed but it isn't supported by ld.lld.
 *
 * NOCROSSREFS_TO(.init .text)
 */

SECTIONS
{
	/*
	 * Set the image origin to a platform specific address. The images are
	 * relocatable but some platforms, e.g. QEMU, load to the same address
	 * and it makes debugging easier if the addresses match the symbols.
	 */
	. = ORIGIN_ADDRESS;

	/*
	 * Collect together the code. This is page aligned so it can be mapped
	 * as executable-only.
	 */
	text_begin = .;
	.init : {
		*(.init.entry)
		*(.init.*)
	}
	.text : {
		*(.text.*)
	}
	text_end = .;

	/*
	 * Collect together read-only data including relocations at the end
	 * which are applied by the entry code.  This is page aligned so it can
	 * be mapped as read-only and non-executable.
	 */
	. = ALIGN(4096);
	rodata_begin = .;
	.rodata : {
		*(.rodata.*)
	}
	/* .rela contains Elf64_Rela entries which contain 8-byte fields so
	 * should be 8-byte aligned. */
	. = ALIGN(8);
	rela_begin = .;
	.rela : {
		*(.rela.*)
	}
	rela_end = .;
	rodata_end = .;

	/*
	 * Collect together the read-write data including .bss at the end which
	 * will be zero'd by the entry code. This is page aligned so it can be
	 * mapped as non-executable.
	 */
	. = ALIGN(4096);
	data_begin = .;
	.data : {
		*(.data)
	}
	/* The entry point code assumes that .bss is 16-byte aligned. */
	. = ALIGN(16);
	bss_begin = .;
	.bss : {
		*(.bss)
		*(COMMON)
	}
	. = ALIGN(16);
	bss_end = .;
	data_end = .;

	/*
	 * Make note of some useful values.
	 */

	/* Note the first page not used in the image. */
	. = ALIGN(4096);
	bin_end = .;

	/* Note the size of the image. This includes everything up to the .bss
	 * as that is initialized to zero by the entry code. */
	image_size = ABSOLUTE(bss_begin - ORIGIN_ADDRESS);
}
