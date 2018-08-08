ENTRY(entry)
SECTIONS
{
	. = ORIGIN_ADDRESS;
	_orig_base = ABSOLUTE(.);

	text_begin = .;
	.init : {
		*(.init.entry)
		*(.init.*)
	}
	.text : {
		*(.text.*)
	}
	text_end = .;

	. = ALIGN(4096);
	rodata_begin = .;
	.rodata : {
		*(.rodata.*)
	}
	.rela : ALIGN(8) {
		rela_begin = .;
		*(.rela .rela*)
		rela_end = .;
	}
	rodata_end = .;

	. = ALIGN(4096);
	data_begin = .;
	.data : {
		*(.data)
	}

	/* The entry point code assumes that bss is 16-byte aligned. */
	.bss ALIGN(16) : {
		file_size = ABSOLUTE(. - ORIGIN_ADDRESS);
		bss_begin = .;
		*(.bss COMMON)
		. = ALIGN(16);
		bss_end = .;
	}
	data_end = .;

	. = ALIGN(4096);
	bin_end = .;
}
