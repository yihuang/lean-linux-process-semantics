# shell.nix — the toolchain `tools/e2e/rwx_flag_ns.sh` needs for the C side.
#
#   nix-shell
#   nix-shell --run 'bash tools/e2e/rwx_flag_ns.sh'
#
# The two compilers the e2e flow needs, from the same nixpkgs revision:
#
#   pkgsCross.riscv64-musl.stdenv.cc  the GNU musl cross GCC that builds the
#       RwxFlagNs SOURCE binary (driver `riscv64-unknown-linux-musl-gcc`,
#       handed to the script as SOURCE_CC; the script has no fallback);
#   pkgs.zig  the TARGET compiler (`zig build-exe`, 0.15.2 on the pinned rev —
#       its `.text`/data are byte-identical to the committed target binary).
#
# CI uses this same shell, with `-I nixpkgs=<pinned archive>` so both versions
# are fixed.
#
# ON aarch64-darwin, READ THIS FIRST: the cross GCC is a *host* tool, and
# cache.nixos.org only carries Linux builds (Hydra does not build darwin), so
# `nix-shell` will COMPILE GCC (15.2.0 on nixos-unstable) from source — tens of
# minutes, not a download.  Use a Linux machine (CI does), a Linux builder, or a
# prebuilt riscv64-linux-musl toolchain (e.g. musl.cc's tarball, ~108 MB) with
# `SOURCE_CC=<prefix>/bin/riscv64-linux-musl-gcc bash tools/e2e/rwx_flag_ns.sh`.
#
# The compiler VERSION is whatever the nixpkgs channel has, not a pinned one:
# the committed source binary is one specific GNU musl build, so a different
# GCC version is expected to emit a different program (same layout).  Use
# `--strict-bytes` on a machine with the original compiler for an exact gate,
# or `--update --update-source` to re-baseline (and re-derive the proof).
{ pkgs ? import <nixpkgs> { } }:
let
  cc = pkgs.pkgsCross.riscv64-musl.stdenv.cc;
in
pkgs.mkShell {
  packages = [ cc pkgs.zig ];
  SOURCE_CC = "${cc}/bin/riscv64-unknown-linux-musl-gcc";
  # REPRODUCE THE COMMITTED BINARY.  nixpkgs' compiler wrapper injects its
  # stdenv hardening and its default PIE/arch choices into every invocation:
  # `-fPIC`, `-pie`, `-fstack-clash-protection`, `-fzero-call-used-regs=used-gpr`,
  # `-fstack-protector-strong`, `-fno-omit-frame-pointer`, `-march=rv64gc`.  On
  # this program they change the RESULT: `flag` is addressed through `auipc`
  # instead of absolute `lui`, `main` grows a 16-byte stack frame, and
  # `e_flags` claims the C extension.  With the cancels below, GCC 15.2 compiles
  # the committed (upstream GNU) PROGRAM BYTES exactly — only the section-table
  # pointer differs — which is what the e2e gate requires.
  #
  # The `_riscv64_unknown_linux_musl` suffix is the wrapper's target-specific
  # variable; the wrapper appends it LAST, which is why these win.
  NIX_CFLAGS_COMPILE_riscv64_unknown_linux_musl =
    "-fno-PIC -fno-pie -fno-stack-clash-protection -fno-stack-protector "
    + "-fzero-call-used-regs=skip -fomit-frame-pointer -fno-strict-overflow";
  NIX_LDFLAGS = "-no-pie";
}
