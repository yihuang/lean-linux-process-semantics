/* musl's `environ` slot.
   The upstream build gets this symbol from musl's libc (`__environ`, 8 bytes
   in .bss); this tree has no riscv64 musl-gcc, and the ONLY thing the source
   binary uses from libc is this one writable slot (the minimal crt stores the
   envp pointer into it).  Defining it here keeps the binary's layout and
   contents identical without linking a libc. */
.section .bss
.globl environ
.align 3
environ:
    .zero 8
