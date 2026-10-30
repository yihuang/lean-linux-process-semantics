/-
  * LinuxProcessSem.Sys.Fs.Readdir — getdents64 (61)

  This file answers to Linux `fs/readdir.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines
  the syscall.  `Specs.lean` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  A spec's monad is `SysSpec SyscallEffect` from `MonadInstances`, fixed
  at the concrete `Model`/`SyscallInput`/`event`.  The 
  `sys_scope` sequencing `x <- c ;; k` is `bind c (fun x => k)` in Lean,
  which is how the one `get_model` step and the `errno_from` step below
  are written.  `ret_only`, `err_ret`, `errno_from` and `sint32` are
  `Sys/Syscall.lean`'s, and `m_fds`/`fd_lookup` are `StateLedger`/
  `StateFd`'s.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Sys.Syscall

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Readdir

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall

/-- getdents64's injectable failure: one environment condition the model
    does not track, and the only one getdents(2) documents that a
    modeled arm could otherwise preempt.  `iterate_dir` (Linux
    fs/readdir.c, v6.18.46) answers -ENOENT for `IS_DEADDIR(inode)` — a
    directory removed since the fd was opened — and does so BEFORE it
    calls the filesystem's `.iterate_shared`, hence before the -EINVAL
    below is reached.

    -EBADF and -ENOTDIR are NOT injectable: both are decided from state
    the model does carry (the fd table, and the fd's kind).  -EFAULT is
    not either: every arm this spec admits is settled before the kernel
    touches the destination buffer — see the note at
    `getdents64_spec`. -/
def getdents64_errnos : List Int := [ENOENT]

/-- The SMALLEST record any directory entry can occupy in a
    `struct linux_dirent64` buffer, in bytes.

    `filldir64` (Linux fs/readdir.c, v6.18.46) computes

      reclen = ALIGN(offsetof(struct linux_dirent64, d_name) + namlen + 1,
                     sizeof(u64))

    and `struct linux_dirent64` (Linux include/linux/dirent.h, v6.18.46)
    is `u64 d_ino; s64 d_off; unsigned short d_reclen; unsigned char
    d_type; char d_name[]`, so `offsetof(..., d_name)` is 19.  A name is
    at least one byte — `verify_dirent_name` (Linux fs/readdir.c,
    v6.18.46) refuses `len <= 0`, and no filesystem emits an empty
    name — so
    `reclen >= ALIGN(19 + 1 + 1, 8) = 24`, with equality for the
    one-byte name ".".

    This is a floor over ALL entries, not a fact about any one of them,
    which is what lets the spec use it without knowing what the
    directory holds. -/
def dirent64_min_reclen : Int := 24

/-- The buffer size AS THE KERNEL COMPARES IT.  `count` arrives declared
    `unsigned int` (`SYSCALL_DEFINE3(getdents64, unsigned int, fd,
    struct linux_dirent64 __user *, dirent, unsigned int, count)`, Linux
    fs/readdir.c, v6.18.46), so the high half of the register is gone
    before anything reads it — the same narrowing `Syscall.fd32`
    describes for a file descriptor.  It is then stored into
    `ctx.count`, which `struct dir_context` (Linux include/linux/fs.h,
    v6.18.46) declares `int`, and `filldir64`'s `reclen > ctx->count` is
    a SIGNED comparison.

    So the two conversions compose into "the low 32 bits, read as two's
    complement", which is exactly `Syscall.sint32` — and the composition
    is observable rather than pedantic: a `count` at or above 2^31 is a
    NEGATIVE `ctx->count`, so `getdents64(dirfd, buf, 0x80000000)` is
    -EINVAL on Linux, not a large successful read.  Comparing the
    unsigned register instead would have admitted a success no kernel
    produces. -/
def getdents64_ctx_count (count : word) : Int := sint32 count

/-- Is the buffer too small for the first entry, whatever that entry
    turns out to be? -/
def getdents64_no_room (count : word) : Bool :=
  decide (getdents64_ctx_count count < dirent64_min_reclen)

/-- `getdents64 fd dirent count`: read directory entries into `dirent`.

    THE SUCCESS ARM IS NOT MODELED, AND CANNOT BE FROM WHAT THIS MODEL
    CARRIES.  A successful call fills the buffer with `struct
    linux_dirent64` records — `d_ino`, `d_off`, `d_reclen`, `d_type` and
    the name — and returns the byte count.  Three INDEPENDENT things
    stand in the way, and closing any one of them leaves the other two:

    - `State.FdDir` IS NULLARY.  It records that the fd names a
      directory and nothing else, so the model cannot tell an fd opened
      on "." from one opened on ".." — the only two paths
      `Open.path_is_dirref` admits.  Enumerating the working directory
      for BOTH is a confident wrong answer for one of them, and the
      model has nothing to branch on.  `Open.openat_spec` answers ".."
      at all only because nothing the model can then do to the fd tells
      the two apart — read is -EISDIR for either, close is close, lseek
      is declined — and this spec is the clause of that argument that
      names getdents64.  A listing arm would break it, not merely be
      wrong on its own.
    - `Fs.Fs` IS A MAP FROM PATH TO CONTENTS and holds no metadata, so
      `d_ino` and `d_type` are not derivable from it, and neither is the
      `d_off` cookie, which is the filesystem's own opaque position.
      That is the same wall `Stat.newfstatat_spec` hits: "A spec that
      answered the call would be inventing the rest".
    - THE KEY SET IS NOT THE DIRECTORY.  Even granting the two above,
      the map's keys do not enumerate the working directory: a real
      EMPTY subdirectory leaves no key at all, "." and ".." are entries
      of every real directory and keys of none, and a key "a/b" implies
      a directory "a" the map cannot hold.  `Namei.unlinkat_spec`'s
      WORLD paragraph states that correspondence and its hole, a
      divergence kept rather than fixed.  A listing read off the
      keys would report a directory Linux would not.

    So the enumerate-the-image shape is declined, and the FAILING side —
    the part of the call that writes nothing — is what is modeled,
    exactly as `Stat.newfstatat_spec` models its own.

    `dirent` IS NOT AN ARGUMENT OF THIS SPEC, and its arity is the
    statement that no modeled arm can deliver a byte, and hence that
    none can fault on the destination either.  `filldir64` reaches
    `user_write_access_begin` only AFTER the `reclen > ctx->count` test,
    so on the one directory arm below the kernel has not touched the
    buffer: `getdents64(dirfd, NULL, 0)` is -EINVAL, not -EFAULT.

    ORDER, following the kernel's exactly (Linux fs/readdir.c,
    v6.18.46, `SYSCALL_DEFINE3(getdents64)` and `iterate_dir`):

    - the fd first.  `CLASS(fd_pos, f)(fd)` is `fdget_pos`, and
      `fd_empty(f)` returns -EBADF before `iterate_dir` is entered, so a
      closed fd is -EBADF whatever kind of object the number would have
      named.  `fd` arrives already truncated to 32 bits (see
      `Syscall.fd32`), so `getdents64(2^32, ...)` names fd 0.
    - then the fd's KIND.  `iterate_dir` opens with

        int res = -ENOTDIR;
        if (!file->f_op->iterate_shared)
                goto out;

      so -ENOTDIR precedes `security_file_permission`,
      `fsnotify_file_perm`, the inode lock and the `IS_DEADDIR` test
      alike.  It is the FIRST thing that function does.
    - then, on a directory, the buffer size, in `filldir64`.

    -ENOTDIR ON EVERY NON-DIRECTORY, and here the model spends nothing.
    `.iterate_shared` is the directory iterator: no file_operations
    table for a non-directory object defines one, so the answer does not
    turn on WHICH object a channel or a file fd is attached to.  That is
    strictly weaker than what `Sync.fsync_spec` needs — its -EINVAL for
    a channel rests on the channel being a pipe, and plain shell
    redirection falsifies it — so the same
    redirection leaves this arm untouched: a regular file on fd 1 is
    -ENOTDIR just as a pipe is.  Checked at v6.18.46: `pipefifo_fops`
    and `pipeanon_fops` (fs/pipe.c), `socket_file_ops` (net/socket.c),
    `ext4_file_operations` (fs/ext4/file.c), `shmem_file_operations`
    (mm/shmem.c), `null_fops` (drivers/char/mem.c) and `tty_fops`
    (drivers/tty/tty_io.c) — not one of those six files contains the
    token `iterate_shared` at all.

    -EINVAL FOR A BUFFER TOO SMALL FOR THE FIRST ENTRY.  `filldir64`
    sets `buf->error = -EINVAL` and returns false on
    `reclen > ctx->count`, which `dir_emit_dots` (Linux
    include/linux/fs.h, v6.18.46) turns into a zero-length iteration and
    `SYSCALL_DEFINE3(getdents64)` then reports, since `buf.prev_reclen`
    is still 0 and the `error = count - buf.ctx.count` rewrite is
    skipped.  `dirent64_min_reclen` bounds `reclen` from below over
    every possible entry, so a `ctx->count` under 24 cannot fit ANY
    entry and the answer does not depend on the directory's contents.

    THAT ARM RESTS ON ONE PREMISE, stated here because it is what a
    later change has to re-check: THE ITERATION EMITS AT LEAST ONE
    ENTRY.  A directory with nothing left to emit returns 0, not
    -EINVAL.  Two facts make it hold:

    - The iteration at position 0 emits "." first.  `dir_emit_dots`
      (Linux include/linux/fs.h, v6.18.46) is the generic opener, and it
      is the FIRST STATEMENT of the readdir every filesystem a modeled
      run can sit on installs: tmpfs's `offset_readdir`, reached through
      `simple_offset_dir_operations` (Linux fs/libfs.c, v6.18.46), and
      sysfs's `kernfs_fop_readdir` (Linux fs/kernfs/dir.c, v6.18.46) and
      procfs's `proc_readdir_de` (Linux fs/proc/generic.c, v6.18.46).
      THIS IS THE BOUND WORTH NAMING, in the shape `Sync.fsync_spec`'s
      directory arm names its own: it holds of THOSE filesystems, not of
      every filesystem, and one whose directory yielded nothing at
      position 0 would answer 0 where this arm says -EINVAL.
    - Every `FdDir` a modeled run can hold IS at position 0.
      `State.FdDir` carries no position field, and nothing modeled gives
      it one: `Open.openat_spec` mints it from a fresh open,
      `ReadWrite.lseek_spec` DECLINES a directory fd,
      `ReadWrite.read_spec` answers -EISDIR without moving anything,
      `Fork.clone_spec` shares a `struct file` neither branch can
      advance, and this spec's own only non-declining directory arm does
      not advance it either — `filldir64` refuses on the size and writes
      nothing at all, `dir_emit_dots` leaves `ctx->pos` at 0 when
      `dir_emit_dot` returns false, and `iterate_dir`'s
      `file->f_pos = ctx->pos` then writes back the 0 it read.

      GIVE `FdDir` A POSITION, or give this spec a success arm that
      advances one, and the premise stops being free: the -EINVAL would
      then have to be conditioned on the position, because a directory
      read to its end answers 0 to the very same call.

    APPROXIMATION, and it is a NARROWING rather than a wrong answer.
    Two untracked conditions sit between the -ENOTDIR and the -EINVAL —
    `security_file_permission`'s LSM verdict and `fsnotify_file_perm`'s
    fanotify permission response — and neither errno is documented for
    getdents(2), so neither is offered here.  Under an LSM that denies
    the read, or a fanotify listener that answers FAN_DENY, this spec
    REJECTS a conforming trace on the directory arm.  (`down_read_killable`'s
    -EINTR is a third, and is unreachable rather than approximated: it
    fires only on a fatal signal, which kills the task before any return
    value reaches userspace.)  The -EBADF and -ENOTDIR arms are behind
    none of the three and are unconditional.

    Nothing is written on any admitted arm, so every effect is a bare
    return with five empty ledgers, and no arm reads user memory either
    — hence no copy-in ledger. -/
def getdents64_spec (fd count : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    match fd_lookup (m_fds m) fd with
    | none => err_ret EBADF
      /- fd not open: `fd_empty`, before `iterate_dir` -/
    | some (FdEntry.FdChannel _) => err_ret ENOTDIR
      /- no `.iterate_shared` on any non-directory -/
    | some (FdEntry.FdFile _ _) => err_ret ENOTDIR
    | some (FdEntry.FdFileW _ _) => err_ret ENOTDIR
    | some (FdEntry.FdFileA _ _) => err_ret ENOTDIR
      /- append mode changes where a write lands, not whether the inode
         has an `.iterate_shared` -/
    | some (FdEntry.FdFileRW _ _) => err_ret ENOTDIR
      /- and neither does the access mode: the same regular file, opened
         O_RDWR -/
    | some (FdEntry.FdPipe _ _) => err_ret ENOTDIR
    | some (FdEntry.FdSocket _) => err_ret ENOTDIR
    | some (FdEntry.FdDevNull _ _) => err_ret ENOTDIR
      /- `null_fops` (drivers/char/mem.c, v6.18.46) has no
         `.iterate_shared`, so `iterate_dir` (fs/readdir.c) answers its
         opening -ENOTDIR -/
    | some FdEntry.FdUrandom => err_ret ENOTDIR
      /- and `urandom_fops` (drivers/char/random.c) has none either: the
         same -ENOTDIR -/
    | some FdEntry.FdDir =>
        if getdents64_no_room count then
          alt (bind (errno_from getdents64_errnos) fun e => err_ret e)
            /- the removed directory -/
            (err_ret EINVAL)
            /- `filldir64`'s own answer -/
        else unmodeled
        /- the listing itself: see the header's three reasons -/

/-! ## Sanity checks

  It is five definitions and the prose above. The checks below are PORT CHECKS, and
  they pin the three computable things the header argues for:

    - the `struct linux_dirent64` layout, and hence that
      `dirent64_min_reclen` really is the smallest record;
    - the signed `ctx->count` read, and the -EINVAL it forces on a
      buffer under 24 bytes (and on a `count` with bit 31 set);
    - the modelled arms of `getdents64_spec` against a concrete model:
      -EBADF for an fd that is not open, -ENOTDIR for every
      non-directory, both the injectable -ENOENT and the deterministic
      -EINVAL on a directory with too small a buffer, and `unmodeled`
      once the buffer could hold an entry. -/

/-- `offsetof(struct linux_dirent64, d_name)`, from the field list quoted
    at `dirent64_min_reclen`: `u64 d_ino; s64 d_off; unsigned short
    d_reclen; unsigned char d_type` is 8 + 8 + 2 + 1 = 19. -/
private def dirent64HeaderBytes : Nat := 8 + 8 + 2 + 1

/-- `ALIGN(n, sizeof(u64))`, the macro `filldir64` applies to the record
    length. -/
private def align8 (n : Nat) : Nat := (n + 7) / 8 * 8

/-- `filldir64`'s
    `reclen = ALIGN(offsetof(struct linux_dirent64, d_name) + namlen + 1,
    sizeof(u64))`.  The `+ 1` is the NUL `verify_dirent_name` requires. -/
private def dirent64Reclen (namlen : Nat) : Nat :=
  align8 (dirent64HeaderBytes + namlen + 1)

/-- The header is 19 bytes: 8 `d_ino`, 8 `d_off`, 2 `d_reclen`, 1
    `d_type`. -/
example : dirent64HeaderBytes = 19 := by decide

/-- The one-byte name "." is the smallest record, and it is exactly
    `dirent64_min_reclen` bytes — which is the claim the -EINVAL arm
    rests on. -/
example : dirent64Reclen 1 = dirent64_min_reclen.toNat := by decide

/-- Two- and nine-byte names: 24 stays the floor, and the rounding is to
    whole 8-byte words. -/
example : dirent64Reclen 2 = 24 := by decide

example : dirent64Reclen 9 = 32 := by decide

/-- The constant itself is the kernel's 24. -/
example : dirent64_min_reclen = 24 := by decide

/-- A buffer of 23 bytes cannot hold the smallest entry: -EINVAL. -/
example : getdents64_no_room 23 = true := by decide

/-- A buffer of 24 can, whatever the entry is. -/
example : getdents64_no_room 24 = false := by decide

/-- The `ctx->count` read is SIGNED, so a `count` at 2^31 is a negative
    `int` — `getdents64(dirfd, buf, 0x80000000)` is -EINVAL on Linux,
    not a large successful read. -/
example : getdents64_ctx_count (BitVec.ofInt 64 2147483648) = -2147483648 := by
  decide

example : getdents64_no_room (BitVec.ofInt 64 2147483648) = true := by decide

/-- …and it is the LOW 32 BITS that are read: a `count` of 2^32 + 24 is
    a `ctx->count` of 24, so the buffer is big enough. -/
example : getdents64_ctx_count (BitVec.ofInt 64 4294967320) = 24 := by decide

example : getdents64_no_room (BitVec.ofInt 64 4294967320) = false := by decide

/-- A tiny fd table for the checks: 0 a channel, 1 a regular file
    (`out`), 2 a directory, 3 a pipe end, 4 `/dev/null`. -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0),
    (2, FdEntry.FdDir),
    (3, FdEntry.FdPipe 0 true),
    (4, FdEntry.FdDevNull true false) ]

/-- The model the checks run in: the fd table above, an empty VM ledger,
    an empty file system, EOF on stdin, no halt and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof []

/-- A syscall input for `getdents64` (61).  The spec reads none of it: it
    is here because a `SysSpec` is a relation on an input as well as a
    model. -/
private def demoInput : SyscallInput :=
  { in_sysno := 61, in_args := [2, 24], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-- A MISSING FD IS -EBADF, and it is the fd lookup that decides: no
    object is examined at all. -/
example :
    getdents64_spec 9 24 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  simp [getdents64_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- A CHANNEL IS -ENOTDIR: no `.iterate_shared` on a non-directory. -/
example :
    getdents64_spec 0 24 demoInput demoModel
      (.ok (mkEffect (errno_ret ENOTDIR) [] []) demoModel []) := by
  simp [getdents64_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- A REGULAR FILE IS -ENOTDIR TOO — the arm plain shell redirection
    leaves untouched: `ext4_file_operations` has no `.iterate_shared`
    either. -/
example :
    getdents64_spec 1 24 demoInput demoModel
      (.ok (mkEffect (errno_ret ENOTDIR) [] []) demoModel []) := by
  simp [getdents64_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- A PIPE END IS -ENOTDIR as well. -/
example :
    getdents64_spec 3 24 demoInput demoModel
      (.ok (mkEffect (errno_ret ENOTDIR) [] []) demoModel []) := by
  simp [getdents64_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- A DIRECTORY WITH A 23-BYTE BUFFER IS -EINVAL: the deterministic arm,
    the one `filldir64`'s own `reclen > ctx->count` test answers. -/
example :
    getdents64_spec 2 23 demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp [getdents64_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, getdents64_no_room, getdents64_ctx_count,
    dirent64_min_reclen, sint32, alt, err_ret, ret_only, pure]

/-- …AND -ENOENT IS ADMISSIBLE FOR THE SAME CALL: `iterate_dir` answers
    it for a removed directory before `filldir64` ever runs, which is
    exactly why the two sit behind an `alt`.  The witness is the one
    element of `getdents64_errnos`; `bind_ok`/`choose_ok`/`alt_l` are the
    introduction lemmas that build it, since `simp` cannot invent a
    witness for the `choose`. -/
example :
    getdents64_spec 2 23 demoInput demoModel
      (.ok (mkEffect (errno_ret ENOENT) [] []) demoModel []) := by
  simp [getdents64_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, getdents64_no_room, getdents64_ctx_count,
    dirent64_min_reclen, sint32, err_ret, ret_only]
  refine alt_l _ _ _ _ _ ?_
  exact bind_ok _ _ demoInput demoModel ENOENT demoModel [] _ demoModel []
    (choose_ok _ ENOENT demoInput demoModel (by decide)) rfl

/-- A DIRECTORY WITH ROOM IS `unmodeled`: the listing itself is what the
    model declines to produce. -/
example : getdents64_spec 2 24 demoInput demoModel .unmodeled := by
  simp [getdents64_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, getdents64_no_room, getdents64_ctx_count,
    dirent64_min_reclen, sint32, unmodeled, err_ret, ret_only]

/-! The four errnos really are the kernel's numbers in the return word —
    the encoding every arm above hands back. -/

example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret ENOTDIR = BitVec.ofInt 64 (-20) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : errno_ret ENOENT = BitVec.ofInt 64 (-2) := by decide

/-- The injectable set is one errno wide, and it is `ENOENT`: neither
    -EBADF nor -ENOTDIR is drawn from it (both are decided from state the
    model carries). -/
example : getdents64_errnos = [ENOENT] := rfl

example : (getdents64_errnos.map errno_ret) = [BitVec.ofInt 64 (-2)] := by
  decide

end LinuxSem.LinuxProcessSem.Sys.Fs.Readdir
