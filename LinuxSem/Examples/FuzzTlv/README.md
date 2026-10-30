# FuzzTlv: no input makes this compiled fuzz target fail

The fuzz-target verification pipeline on a small program:

    C source → riscv64 ELF → statement over the ELF's bytes → machine-checked proof

`source/fuzz_tlv.c` is a driver and a parser for `[tag][len][value]` records. It
builds two ways: `program.fixed.elf` with `-DFIXED`, `program.buggy.elf` without.

| theorem | result |
| --- | --- |
| `FixedProof.plain_halts_holds`, `plain_halts_may_fail_holds` | the fixed build meets both statements of `Statements.lean` |
| `BuggyRefutation.buggy_halts_refuted`, `buggy_halts_may_fail_refuted` | the buggy build meets neither; its counterexample is empty standard input |

The headers of those files explain each argument. To check it all:

    lake build LinuxSem.Examples.FuzzTlv.FixedProof LinuxSem.Examples.FuzzTlv.BuggyRefutation
    nix-shell -p zig qemu --run 'bash tools/e2e/fuzz_tlv.sh --require-qemu'

To change the program, rebuild the ELFs with `source/build_flags.txt`, regenerate
the facts with `tools/e2e/gen_step_facts.py`, delete the `Images` module's build
artifacts (`embedElf%` reads the ELF outside Lean's build graph), and redo the proofs.

## What this does not cover

These limits make it narrower than a statement about a real OSS-Fuzz target, and
most are the work that remains.

- **No C library.** A real target links musl, so its proof must also cover the C
  start-up, `malloc`, and the `mmap` and `brk` calls behind it.
- **Standard input, not a file.** A full driver opens `argv[1]`, and
  `OssVerify.HaltsLib` has rules only for `read` and `exit_group`.
- **A plain build only.** With no sanitizer build there is no agreement statement,
  and a stray read inside a mapping is not an error. The buffer ends at the end of
  the mapping so that an overrun faults.
- **A restricted build.** A 256-byte buffer, no compressed instructions (the step
  lemmas are for 4-byte instructions), and no frame pointers.
- **The proof is by hand.** It does not extrapolate to a binary of thousands of
  instructions; that needs the reflective executor in `Common/` or generated proofs.
