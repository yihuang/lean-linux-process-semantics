#!/usr/bin/env bash
#
# tools/e2e/rwx_flag_ns.sh — rebuild the RwxFlagNs example from its SOURCES
#
# The committed artifacts are the two BINARIES:
#
#   source/program.c   --riscv64-linux-musl-gcc-->  program.src.elf
#   target/program.zig --zig build-exe---------->  program.tgt.elf
#
# and `SourceMemImage.lean`/`TargetMemImage.lean` read those files at
# elaboration time (`embedElf%`, Common/EmbedElf → Common/ElfImage).  This
# script rebuilds both with the command lines the upstream repository
# documents, then compares each rebuilt binary with its committed counterpart
# AT THE LOADER LEVEL (tools/e2e/compare_elfs.py): the page-rounded segment
# extents and permissions, the entry point, the AT_PHDR the kernel derives, and
# then the bytes — per PT_LOAD, its own file extent separately from the page
# slack around it.
#
# THE TOOLCHAINS (both required; there is no fallback)
#
#   zig                     builds the target (0.15.2 from nixpkgs' `pkgs.zig`;
#                           its `.text`/data are byte-identical to the
#                           committed target binary).
#   riscv64-linux-musl-gcc  builds the source (`SOURCE_CC` overrides; the
#                           nixpkgs cross driver is named
#                           `riscv64-unknown-linux-musl-gcc` and is found too).
#
# Both come from nixpkgs; `shell.nix` at the repository root provides both,
# the cross compiler also as `SOURCE_CC`:
#
#     nix-shell --run 'bash tools/e2e/rwx_flag_ns.sh'
#     nix shell nixpkgs#pkgsCross.riscv64-musl.stdenv.cc nixpkgs#zig -c bash tools/e2e/rwx_flag_ns.sh
#
# The script fails, with that hint, rather than silently building the source
# with a different compiler: the committed source binary is a GNU musl build,
# and a clang build is a different program (the old `zig cc` fallback is gone).
#
# WHAT THE COMPARISON MEANS
#
#   layout identical, program bytes identical   -> exit 0 (the image is the same
#       program; only the section header table, which the loader never reads and
#       the program never touches, moved)
#   layout identical, page images identical     -> exit 0 (exact reproduction;
#       `--strict-bytes` demands this)
#   layout identical, program bytes differ      -> FAIL for BOTH sides:
#       `shell.nix` pins the toolchain (cross GCC + flags) and was measured to
#       reproduce the committed source binary's program bytes exactly (only the
#       section-table pointer and `e_flags` differ, both masked), and the target
#       likewise.  `--allow-program-drift` is the escape hatch for trying a
#       different toolchain.
#   layout differs                              -> FAIL (the recipe or the
#       committed binary is wrong)
#
# The "program bytes" check masks the ELF header's section-table bookkeeping
# (`e_shoff`/`e_shentsize`/`e_shnum`/`e_shstrndx`) and looks only at each
# PT_LOAD's own file extent: that is what a CI gate can hold across compiler
# versions.  `--allow-program-drift` drops the target's program check, and
# `--require-source-program` ADDS the source's (for a host whose GNU compiler is
# the one the committed binary was built with — the `probe` CI job uses it).
# `--only=source|target|both` (default both) restricts which side is built and
# compared, so the source can be probed without zig and vice versa.
#
# RE-BASELINING (`--update`)
#
# Editing a program (or its flags) makes the committed binaries stale.  Rather
# than only failing, `--update` writes the rebuilt binaries back into the repo:
#
#     bash tools/e2e/rwx_flag_ns.sh --update                 # target only
#     bash tools/e2e/rwx_flag_ns.sh --update --update-source # ... and the source
#
# It writes a side only when that side's PROGRAM changed (or when `--force` is
# given), so on a clean checkout it is a no-op and leaves the committed
# binaries — including their section tables — untouched.  Guards:
#
#   - a LAYOUT change (page extents/permissions, entry, phdr record) changes the
#     example's SHAPE, which the proof's statements are written against:
#     `--update` refuses it without `--force`;
#   - the SOURCE binary is only re-baselined when `--update-source` is given:
#     the committed one is a specific GNU build, and replacing it makes
#     `RwxFlagNsSource.lean`'s derivation stale by construction.
#
# After writing, the two image modules' build artifacts are deleted — `embedElf%`
# reads the ELF at elaboration and Lean's build graph does not see that read —
# and the script prints the Lean command to run.  The PROOF is stated over the
# old instruction stream: when a program changed, `RwxFlagNsSource.lean` /
# `RwxFlagNsTarget.lean` must be re-derived (and `RwxFlagNsDefs.lean`'s
# `stext_lo`/`stext_hi` and `flag`/`__environ` addresses re-checked) — the
# modules' `decide` checks fail until then, which is the intended signal.
set -euo pipefail
cd "$(dirname "$0")/../.."          # repository root

EX="LinuxSem/Examples/RwxFlagNs"
OUT=".lake/e2e/rwx"
mkdir -p "$OUT"
ROOT="$(pwd)"

STRICT_BYTES=0
ALLOW_PROGRAM_DRIFT=0
REQUIRE_SOURCE_PROGRAM=0
DO_UPDATE=0
UPDATE_SOURCE=0
FORCE=0
ONLY=both
for arg in "$@"; do
  case "$arg" in
    --strict-bytes) STRICT_BYTES=1 ;;
    --allow-program-drift) ALLOW_PROGRAM_DRIFT=1 ;;
    --require-source-program) REQUIRE_SOURCE_PROGRAM=1 ;;  # now the default; kept for scripts
    --update) DO_UPDATE=1 ;;
    --update-source) UPDATE_SOURCE=1 ;;
    --force) FORCE=1 ;;
    --only=source) ONLY=source ;;
    --only=target) ONLY=target ;;
    --only=both) ONLY=both ;;
    *) echo "usage: $0 [--strict-bytes | --allow-program-drift] [--require-source-program] [--only=source|target|both] [--update [--update-source] [--force]]" >&2; exit 2 ;;
  esac
done
if [ "$REQUIRE_SOURCE_PROGRAM" = 1 ] && [ "$STRICT_BYTES" = 1 ]; then
  echo "--strict-bytes already demands the page images be identical; --require-source-program is redundant." >&2
  exit 2
fi
# (--require-source-program is accepted but no longer needed: the source's
# program bytes are gated by default now that shell.nix pins the toolchain.)
if [ "$DO_UPDATE" = 1 ] && [ "$STRICT_BYTES" = 1 ]; then
  echo "--update writes the rebuilt binaries; --strict-bytes only checks them. Pick one." >&2
  exit 2
fi
if [ "$UPDATE_SOURCE" = 1 ] && [ "$DO_UPDATE" = 0 ]; then
  echo "--update-source only makes sense together with --update." >&2
  exit 2
fi

warn() { printf '\033[33mWARN\033[0m %s\n' "$*"; }
fail() { printf '\033[31mFAIL\033[0m %s\n' "$*" >&2; exit 1; }

NIX_HINT="nix shell nixpkgs#pkgsCross.riscv64-musl.stdenv.cc -c bash tools/e2e/rwx_flag_ns.sh"

BUILD_SOURCE=1; BUILD_TARGET=1
[ "$ONLY" = target ] && BUILD_SOURCE=0
[ "$ONLY" = source ] && BUILD_TARGET=0

# The source compiler: required, no fallback.  `SOURCE_CC` wins; otherwise the
# two names the toolchains use (musl.cc / distro vs nixpkgs' cross driver).
if [ "$BUILD_SOURCE" = 0 ]; then
  CC=
elif [ -n "${SOURCE_CC:-}" ]; then
  CC="$SOURCE_CC"
elif command -v riscv64-linux-musl-gcc >/dev/null 2>&1; then
  CC=riscv64-linux-musl-gcc
elif command -v riscv64-unknown-linux-musl-gcc >/dev/null 2>&1; then
  CC=riscv64-unknown-linux-musl-gcc
else
  fail "no riscv64-linux-musl-gcc on PATH (the source binary is a GNU musl build; this script does not fall back to another compiler).
  Install one, e.g. from nixpkgs:
      $NIX_HINT
  or \`nix-shell\` at the repository root (shell.nix), or set SOURCE_CC to one.
  (On aarch64-darwin nixpkgs has no cached cross GCC, so shell.nix BUILDS it
  from source — use a Linux host/CI, or a prebuilt toolchain such as musl.cc's
  riscv64-linux-musl-cross, with SOURCE_CC set.)"
fi
if [ "$BUILD_SOURCE" = 1 ]; then
  command -v "$CC" >/dev/null 2>&1 || fail "SOURCE_CC=$CC is not executable"
  # no `| head -1`: `pipefail` turns the SIGPIPE a compiler gets when `head`
  # exits into a script failure (observed with zig's long `--version` output).
  CC_VERSION=$("$CC" --version 2>/dev/null || true)
  CC_VERSION=${CC_VERSION%%$'\n'*}
fi

if [ "$BUILD_TARGET" = 1 ]; then
  ZIG="${ZIG:-zig}"
  command -v "$ZIG" >/dev/null 2>&1 || fail "no zig on PATH (the target is built with \`zig build-exe\`; \`nix-shell\` at the repository root provides it — shell.nix)"
fi

# ---------------------------------------------------------------- 1. source
if [ "$BUILD_SOURCE" = 1 ]; then
  echo "== 1/3  source: $EX/source/program.c"
  echo "         with $CC ($CC_VERSION)"
  # The upstream flags, verbatim — except that `-Wl,--no-warn-rwx-segments`
  # only silences a warning the linker emits for RWX segments, and binutils
  # before 2.39 rejects the option outright (musl.cc's 2021 toolchain ships
  # 2.37).  Probe the linker once and drop the flag when it is not accepted, so
  # an old-but-correct toolchain is not reported as a build failure.
  LDFLAGS=$(grep -hv '^#' "$EX/source/ldflags.txt")
  CFLAGS=
  if [ -f "$EX/source/cflags.txt" ]; then
    CFLAGS=$(grep -hv '^#' "$EX/source/cflags.txt")
  fi
  RWX_FLAG='-Wl,--no-warn-rwx-segments'
  if printf '%s\n' "$LDFLAGS" | grep -q -- "$RWX_FLAG"; then
    printf 'int main(void) { return 0; }\n' > "$OUT/linkprobe.c"
    if ! "$CC" "$RWX_FLAG" -o "$OUT/linkprobe" "$OUT/linkprobe.c" >/dev/null 2>&1; then
      warn "this toolchain's linker rejects $RWX_FLAG (binutils < 2.39);"
      warn "dropping it — it only silences the RWX-segment warning."
      LDFLAGS=$(printf '%s\n' "$LDFLAGS" | grep -v -- "$RWX_FLAG")
    fi
  fi
  # shellcheck disable=SC2086
  ( cd "$EX/source" && "$CC" -std=gnu17 -march=rv64imafd -Os -static \
      -nostartfiles -fno-builtin -fno-strict-aliasing $CFLAGS $LDFLAGS \
      ../../crt/_start.S program.c -o "$ROOT/$OUT/program.src" )
fi

# ---------------------------------------------------------------- 2. target
if [ "$BUILD_TARGET" = 1 ]; then
  echo "== 2/3  target: $EX/target/program.zig"
  # the upstream command line: zig build-exe, freestanding, flags from flags.txt
  TGT_FLAGS=$(grep -hv '^#' "$EX/target/flags.txt" | tr '\n' ' ')
  # shellcheck disable=SC2086
  "$ZIG" build-exe "$EX/target/program.zig" $TGT_FLAGS \
    -target riscv64-linux-none -femit-bin="$OUT/program.tgt"
fi

# ---------------------------------------------------------------- 3. compare
echo "== 3/3  compare the rebuilt binaries with the committed ones (loader level)"
drift=0
updated=0
skipped=0
for pair in "src:source" "tgt:target"; do
  tag=${pair%%:*}; kind=${pair##*:}
  [ "$kind" = source ] && [ "$BUILD_SOURCE" = 0 ] && continue
  [ "$kind" = target ] && [ "$BUILD_TARGET" = 0 ] && continue
  # In read-only mode BOTH sides' program bytes are required: `shell.nix` pins
  # the toolchain that reproduces them.  `--allow-program-drift` drops the
  # check, and `--strict-bytes` replaces it with page-image equality.
  # `--update` asks for the program check on both sides, to learn whether a
  # side actually changed.
  require_program=0
  if [ "$STRICT_BYTES" = 0 ] && [ "$ALLOW_PROGRAM_DRIFT" = 0 ]; then
    require_program=1
  fi
  args=(--rebuilt "$OUT/program.$tag" --committed "$EX/program.$tag.elf" --kind "$kind")
  [ "$require_program" = 1 ] && args+=(--require-program-identical)

  rc=0
  python3 tools/e2e/compare_elfs.py "${args[@]}" || rc=$?

  if [ "$DO_UPDATE" = 1 ]; then
    case $rc in
      0) echo "  $kind: program unchanged; committed binary left as it is" ;;
      1)
        if [ "$FORCE" = 0 ]; then
          fail "$kind: the LAYOUT changed; that changes the example's shape (the proof's statements) — re-baseline by hand, or pass --force"
        fi
        cp "$OUT/program.$tag" "$EX/program.$tag.elf"
        echo "  $kind: UPDATED $EX/program.$tag.elf (layout changed, --force)"
        updated=1 ;;
      2|3)
        if [ "$kind" = source ] && [ "$UPDATE_SOURCE" = 0 ]; then
          skipped=1
          warn "source: this compiler emits a different program than the committed"
          warn "binary ($CC_VERSION).  The committed source build is pinned; pass"
          warn "--update-source to re-baseline it (and expect to re-derive"
          warn "RwxFlagNsSource.lean)."
        else
          cp "$OUT/program.$tag" "$EX/program.$tag.elf"
          echo "  $kind: UPDATED $EX/program.$tag.elf"
          updated=1
        fi ;;
      *) fail "$kind: comparison failed" ;;
    esac
    continue
  fi

  case $rc in
    0)
      if [ "$STRICT_BYTES" = 1 ]; then
        echo "  $kind: committed binary REPRODUCED exactly"
      elif [ "$require_program" = 1 ]; then
        echo "  $kind: layout + program bytes REPRODUCED (section table ignored)"
      else
        echo "  $kind: layout REPRODUCED"
      fi ;;
    2)
      drift=1
      if [ "$STRICT_BYTES" = 1 ]; then
        warn "$kind: page images differ (--strict-bytes measures exactly that;"
        warn "only the compiler the binary was built with reproduces them)."
      else
        warn "$kind: same image LAYOUT, different page bytes; see the"
        warn "per-segment lines above.  The committed source binary is one"
        warn "specific GNU musl build: install that compiler (and pass"
        warn "--require-source-program, or --strict-bytes) for an exact gate,"
        warn "or re-baseline with --update --update-source."
      fi ;;
    3)
      fail "$kind: the rebuilt binary is a DIFFERENT PROGRAM from the committed one (see above); re-baseline it (--update) or pass --allow-program-drift" ;;
    *) fail "$kind: the rebuilt binary has a DIFFERENT LAYOUT from the committed one" ;;
  esac
done

if [ "$DO_UPDATE" = 1 ]; then
  if [ "$updated" = 1 ]; then
    # `embedElf%` reads the ELF at elaboration time and Lean's build graph
    # cannot see that read: drop the image modules' artifacts, or the build
    # would keep using the image it parsed last time.
    for mod in SourceMemImage TargetMemImage; do
      for ext in olean olean.hash ilean ilean.hash trace; do
        rm -f ".lake/build/lib/lean/LinuxSem/Examples/RwxFlagNs/$mod.$ext"
      done
    done
    cat <<'EOF'

Updated the committed binaries. Next:

    lake build LinuxSem.Examples.RwxFlagNs.Proof

The proof is stated over the OLD instruction stream.  If a program changed,
re-derive RwxFlagNsSource.lean / RwxFlagNsTarget.lean and re-check
RwxFlagNsDefs.lean's stext_lo/stext_hi and the flag/__environ addresses; the
image modules' decide checks fail (by design) until that is done.
EOF
  elif [ "$skipped" = 1 ]; then
    echo "Nothing written (the source was skipped; see the WARN above)."
  else
    echo "Nothing to update: the committed binaries already describe the sources."
  fi
  exit 0
fi

if [ "$drift" = 1 ] && [ "$STRICT_BYTES" = 1 ]; then
  fail "byte-identical reproduction was requested (--strict-bytes) and failed"
fi

if [ "$drift" = 1 ]; then
  echo "OK (layout verified; see WARN lines above for byte-level toolchain drift)"
else
  echo "OK"
fi
