// Target translation of rwx-flag: store 5 into a writable global byte,
// load it back, and exit with it.  The layout point is entirely on the
// SOURCE side (its link produces a single RWX LOAD segment — see
// source/rwx.lds); this target is an ordinary lld-linked binary with
// immutable code, so the pair also exercises a mixed proof: w+x fetch on
// one side, the static fast path on the other.
const linux = @import("std").os.linux;

var flag: u8 = 7;

pub export fn _start() callconv(.c) noreturn {
    const p: *volatile u8 = &flag;
    p.* = 5;
    const code: u64 = p.*;
    _ = linux.syscall1(.exit, code);
    unreachable;
}
