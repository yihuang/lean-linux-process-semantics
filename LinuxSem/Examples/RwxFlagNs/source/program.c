/* rwx-flag: the RWX-segment (w+x) exercise.
   Store 5 into a byte of initialized writable data, load it back, and
   exit with it.  The interesting part is not the program but its LINK:
   source/ldflags.txt replaces the default -z separate-code flags with
   an explicit one-segment layout (source/rwx.lds), so the ELF headers,
   .text, and the writable data all share a single RWX LOAD segment —
   the layout GNU ld's default -z noseparate-code merges small binaries
   into.  Every instruction fetch of this binary therefore goes through
   the model's overlay-aware w+x fetch (RiscvSemantics.code_read_ov),
   and the two stores (musl's __environ slot in .bss, and `flag`) land
   in the SAME segment the code executes from — legal, because the
   segment is writable — without ever touching the code bytes (no
   self-modifying code). */

static volatile unsigned char flag = 7;

int main(int argc, char **argv) {
    flag = 5;
    return flag;
}
