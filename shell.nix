# shell.nix — the toolchain `tools/e2e/rwx_flag_ns.sh` needs for the C side.
#
#   nix-shell
#   nix-shell --run 'bash tools/e2e/rwx_flag_ns.sh'
#
# nixpkgs' riscv64-linux-musl cross GCC (driver:
# `riscv64-unknown-linux-musl-gcc`, handed to the script as SOURCE_CC).  That is
# the compiler the RwxFlagNs source binary is built with; the script has no
# fallback, so it is not optional.  Zig — the target's compiler — is not in this
# shell; install it separately (CI pins 0.14.1).
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
  packages = [ cc ];
  SOURCE_CC = "${cc}/bin/riscv64-unknown-linux-musl-gcc";
}
