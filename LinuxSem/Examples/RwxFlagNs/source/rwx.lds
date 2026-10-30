/* One RWX LOAD segment holding the ELF headers, .text, and the writable
   data -- the -z noseparate-code merged layout, produced deterministically
   (current GNU ld versions only merge input-dependently).  FILEHDR/PHDRS
   keep the program header table mapped, which the model publishes as
   AT_PHDR (Equivalence.image_phdrs_readable). */
PHDRS { seg PT_LOAD FLAGS(7) FILEHDR PHDRS; }
ENTRY(_start)
SECTIONS {
  . = 0x10000 + SIZEOF_HEADERS;
  . = ALIGN(4);
  .text : { *(.text*) } :seg
  .rodata : { *(.rodata*) *(.srodata*) }
  .data : { *(.data*) *(.sdata*) }
  __global_pointer$ = . + 0x800;
  .bss : { *(.bss*) *(.sbss*) *(COMMON) }
  /DISCARD/ : { *(.comment) *(.riscv.attributes) *(.eh_frame*) *(.note*) }
}
