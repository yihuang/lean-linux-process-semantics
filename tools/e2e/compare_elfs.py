#!/usr/bin/env python3
"""Compare two riscv64 ELF binaries the way the MODEL loads them.

The RwxFlagNs example is now stated over committed ELF files
(`LinuxSem/Examples/RwxFlagNs/program.{src,tgt}.elf`), read at elaboration time
by `embedElf%`.  So "did this host reproduce the committed binary?" is a
question about the two files as ELF, not about generated Lean modules.

What is compared, and why exactly this:

  1. LAYOUT — for every mapped PT_LOAD, the page-rounded extent
     `[round_down(p_vaddr), round_up(p_vaddr + p_memsz))` and its permission
     string; plus `e_entry`, `e_phnum`/`e_phentsize`, and the AT_PHDR the
     kernel would derive.  These are the facts the proofs' statements are
     written against.
  2. BYTES — each segment's page image, computed with `elf_load`'s rule
     (pages `[round_down(p_vaddr), round_up(p_vaddr + p_filesz))` from the
     file, bss zeroed past `p_vaddr + p_filesz`, zeros past EOF), and per
     PT_LOAD the bytes of its own FILE extent `[p_vaddr, p_vaddr + p_filesz)`.

  The second per-segment line is what distinguishes "the program is the same"
  from "the toolchain wrote a different section header table": a rebuilt
  binary whose `.text`/`.data` extents are byte-identical loads and runs
  identically even though the ELF section table (never read by the program)
  moved.

  `--require-program-identical` adds a third check: the bytes each PT_LOAD
  takes from its own FILE image must be identical, after masking the ELF
  header's section-table bookkeeping (`e_shoff`/`e_shentsize`/`e_shnum`/
  `e_shstrndx`).  That is the check a CI gate can make across compilers: the
  section header table is not loaded, not executed and not read by the
  program, and no two toolchains agree on where it goes — while the code and
  data a program runs on must not move.  The page SLACK around a segment is
  deliberately not part of this check for the same reason.

Exit codes: 0 identical, 2 layout identical but bytes differ, 3 layout
identical and bytes differ but `--require-program-identical` was given and the
program bytes differ, 1 layout differs (or a file cannot be read).
"""
import argparse
import struct
import sys

PAGE = 4096
PT_LOAD = 1

# ELF64 header fields the LOADER does not act on, zeroed by
# `--require-program-identical`:
#   - `e_shoff`/`e_shentsize`/`e_shnum`/`e_shstrndx` (0x28, 0x3a..0x40): where
#     the section header table is.  Not part of the image a program runs on, and
#     no two toolchains place it identically.
#   - `e_flags` (0x30): the float-ABI and RVC declaration.  The kernel ignores
#     it; GNU ld derives it from the LINKED LIBC's attributes, so it differs
#     whenever the libc was built with a different `-march` even though the code
#     and data are byte-identical (nixpkgs' musl is rv64gc, the upstream one was
#     not).
# Everything else in the file extent — every instruction and data byte the
# program touches — is compared.
SHDR_FIELDS = ((0x28, 8), (0x30, 4), (0x3a, 2), (0x3c, 2), (0x3e, 2))


def parse(path):
    d = open(path, 'rb').read()
    if d[:4] != b'\x7fELF' or d[4] != 2 or d[5] != 1:
        raise SystemExit(f"{path}: not a little-endian ELF64 file")
    entry = struct.unpack_from('<Q', d, 0x18)[0]
    phoff = struct.unpack_from('<Q', d, 0x20)[0]
    phentsize = struct.unpack_from('<H', d, 0x36)[0]
    phnum = struct.unpack_from('<H', d, 0x38)[0]
    phdrs = []
    for i in range(phnum):
        o = phoff + i * phentsize
        ptype, flags = struct.unpack_from('<II', d, o)
        off, va, _pa, fs, ms, _al = struct.unpack_from('<QQQQQQ', d, o + 8)
        perms = ''.join(c if flags & bit else '-' for bit, c in ((4, 'r'), (2, 'w'), (1, 'x')))
        phdrs.append(dict(ptype=ptype, perms=perms, off=off, va=va, fs=fs, ms=ms))
    loads = [p for p in phdrs if p['ptype'] == PT_LOAD and p['ms'] > 0]
    return dict(data=d, entry=entry, phentsize=phentsize, phnum=phnum, phdrs=phdrs, loads=loads)


def page_image(elf, seg):
    """elf_load's mapped bytes for one PT_LOAD, page-rounded."""
    lo = seg['va'] - seg['va'] % PAGE
    hi = (seg['va'] + seg['ms'] + PAGE - 1) // PAGE * PAGE
    n = hi - lo
    delta = seg['va'] - lo
    if seg['fs'] == 0:
        return lo, hi, bytes(n)
    file_lo = seg['off'] - delta
    span = (delta + seg['fs'] + PAGE - 1) // PAGE * PAGE
    mapped = bytearray(n)
    for i in range(min(span, n)):
        fo = file_lo + i
        if 0 <= fo < len(elf['data']):
            mapped[i] = elf['data'][fo]
    if seg['ms'] > seg['fs']:
        for i in range(delta + seg['fs'], n):
            mapped[i] = 0
    return lo, hi, bytes(mapped)


def at_phdr(elf, phoff):
    # the kernel's loop has no break: the LAST covering PT_LOAD wins
    addr = None
    for s in elf['loads']:
        if s['off'] <= phoff < s['off'] + s['fs']:
            addr = s['va'] + (phoff - s['off'])
    return addr


def layout(elf, phoff):
    """The facts the proofs' statements are written against.  `p_filesz` is
    NOT one of them: it belongs to the byte comparison (a different compiler
    can emit a different-sized text section, which is a different PROGRAM, but
    the same image LAYOUT)."""
    segs = []
    for s in elf['loads']:
        lo, hi, _img = page_image(elf, s)
        segs.append((lo, hi - lo, s['perms']))
    return dict(segs=segs, entry=elf['entry'], phentsize=elf['phentsize'],
                phnum=elf['phnum'], at_phdr=at_phdr(elf, phoff))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rebuilt', required=True)
    ap.add_argument('--committed', required=True)
    ap.add_argument('--kind', required=True)
    ap.add_argument('--require-program-identical', action='store_true',
                    help="also require each PT_LOAD's own file-extent bytes to "
                         "match, ignoring the ELF header's section-table fields")
    a = ap.parse_args()

    ra, ca = parse(a.rebuilt), parse(a.committed)
    # e_phoff is not kept by parse(); re-read it for the AT_PHDR derivation
    phoff_r = struct.unpack_from('<Q', ra['data'], 0x20)[0]
    phoff_c = struct.unpack_from('<Q', ca['data'], 0x20)[0]
    la, lc = layout(ra, phoff_r), layout(ca, phoff_c)

    if la['segs'] != lc['segs'] or la['entry'] != lc['entry'] \
            or la['phentsize'] != lc['phentsize'] or la['phnum'] != lc['phnum'] \
            or la['at_phdr'] != lc['at_phdr']:
        print(f"  {a.kind}: LAYOUT DIFFERS", file=sys.stderr)
        for k in ('segs', 'entry', 'phentsize', 'phnum', 'at_phdr'):
            if la[k] != lc[k]:
                print(f"    {k}: rebuilt {la[k]} / committed {lc[k]}", file=sys.stderr)
        return 1

    print(f"  {a.kind}: layout identical (segments "
          f"{[(hex(lo), hex(sz), p) for lo, sz, p in lc['segs']]}, "
          f"entry {hex(lc['entry'])}, AT_PHDR {hex(lc['at_phdr']) if lc['at_phdr'] else None})")

    identical = True
    for i, (sra, sca) in enumerate(zip(ra['loads'], ca['loads'])):
        lo_a, _hi_a, img_a = page_image(ra, sra)
        lo_c, _hi_c, img_c = page_image(ca, sca)
        n = min(len(img_a), len(img_c))
        diffs = [k for k in range(n) if img_a[k] != img_c[k]]
        if diffs:
            identical = False
            print(f"  {a.kind}: segment {i} (page {hex(lo_c)}): page image differs "
                  f"in {len(diffs)} of {n} bytes; first at {hex(lo_c + diffs[0])}")
        else:
            print(f"  {a.kind}: segment {i} (page {hex(lo_c)}): page image IDENTICAL")
        # the segment's own file extent -- the program's own bytes
        ext_a = [img_a[sra['va'] - lo_a + k] for k in range(sra['fs'])]
        ext_c = [img_c[sca['va'] - lo_c + k] for k in range(sca['fs'])]
        bad = [k for k in range(min(len(ext_a), len(ext_c))) if ext_a[k] != ext_c[k]]
        verdict = 'IDENTICAL' if not bad else f"differs in {len(bad)} byte(s); first at {hex(sca['va'] + bad[0])}"
        print(f"  {a.kind}: segment {i}: file extent [{hex(sca['va'])}, {hex(sca['va'] + sca['fs'])}) {verdict}")
    if a.require_program_identical:
        def masked(elf):
            d = bytearray(elf['data'])
            for off, n in SHDR_FIELDS:
                for i in range(off, min(off + n, len(d))):
                    d[i] = 0
            return d
        ma, mc = masked(ra), masked(ca)
        bad_program = False
        for i, (sra, sca) in enumerate(zip(ra['loads'], ca['loads'])):
            ea = [ma[sra['off'] + k] for k in range(sra['fs'])]
            ec = [mc[sca['off'] + k] for k in range(sca['fs'])]
            bad = [k for k in range(min(len(ea), len(ec))) if ea[k] != ec[k]]
            if len(ea) != len(ec) or bad:
                bad_program = True
                where = (f"first at {hex(sca['va'] + bad[0])}" if bad
                         else f"length {len(ea)} vs {len(ec)}")
                print(f"  {a.kind}: segment {i}: PROGRAM BYTES DIFFER "
                      f"(file extent [{hex(sca['va'])}, {hex(sca['va'] + sca['fs'])}), {where})",
                      file=sys.stderr)
        if bad_program:
            return 3
        print(f"  {a.kind}: program bytes identical (section-table bookkeeping masked)")
        # in this mode the page slack is informational: the program is the same
        return 0
    return 0 if identical else 2


if __name__ == '__main__':
    sys.exit(main())
