/-
  * LinuxSem.Checks.VmMapsDisjoint.Chain.Arms — the FIRST link
    of the dispatcher chain: every arm of `checked_table` preserves `vm_wf`.

  WHY THIS MODULE EXISTS, and why it is separate.  The
  `Checks/VmMapsDisjoint.v` ends with

      Definition arm_preserves_vm (c : CheckedArm) : Prop := ...
      Theorem checked_table_preserves_vm : Forall arm_preserves_vm checked_table
      Corollary check_syscall_preserves_vm_wf : ...
      Corollary syscall_spec_preserves_vm_wf : ...
      Corollary base_unique_after_syscall : ...

  which is the payoff of PART 3: 77 frame lemmas about individual arms turned
  into ONE statement about the whole syscall surface.  It was deferred while
  the frames were missing.  The frames are all in the tree now (see
  `Frames.lean`, `Frames/Wide.lean`, `Frames/CostlyA.lean` … `CostlyF.lean`),
  so the table induction is writable.

  It is a SEPARATE module from `Chain.lean` for the reason the notes
  measured: this module imports all nine frame modules, so its rebuild cost is
  the sum of nothing new — every proof below is three lines against an
  already-proved frame — while `Chain.lean` (the `Forall` and the four
  dispatcher corollaries) is small and cheap to re-elaborate.  Editing a
  corollary therefore does not re-check this file, and editing an arm lemma
  does not re-check the writers.

  THE SHAPE.  An arm's `ca_check` field is a lambda around its checker
  (`ca_check := fun i eff m => check_getcwd (in_arg i 1) eff m`), so
  `arm_preserves_vm arm_X` is one `simp only [arm_X] at H` (the arm's own
  TERM-level equation) followed by the arm's frame
  lemma applied to `m_vmmaps m' = m_vmmaps m`.  No arm needs its own
  invariant argument: 74 arms have their own frame, 11 share one
  (`check_setid_frame` covers setgid/setuid, `check_setresid_frame`
  setresuid/setresgid, `check_getid_frame` getuid/geteuid/getgid/getegid,
  `check_accept4_frame` accept, `check_exit_frame` exit_group,
  `check_fsync_frame` fdatasync), and `brk` is `check_brk_preserves` — the one
  writer whose PRESERVATION is proved here rather than in `Chain/Writers.lean`
  because it lives in `Core.lean` beside `brk_grant_wf`.

  The four remaining writers (`munmap`, `mremap`, `mmap`, `mprotect`) are NOT
  frames — they rebuild the ledger — so their arm lemmas live in
  `Chain.lean`, on top of `Chain/Writers.lean`'s `check_*_preserves`.

  NO proof hole, and no `decide` on the invariant: `arm_preserves_vm` is a
  `∀ … → Prop` over the checker FIELD, so it is not a decidable proposition
  and must be APPLIED, which is what the per-arm lemmas do.
-/

import LinuxSem.Checks.VmMapsDisjoint.Core
import LinuxSem.Checks.VmMapsDisjoint.Frames
import LinuxSem.Checks.VmMapsDisjoint.Frames.Wide
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyA
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyB
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyC
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyD
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyE
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyF

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.Checks.VmMapsDisjoint
open LinuxSem.Checks.Sys.Kernel.Signal

namespace LinuxSem.Checks.VmMapsDisjoint

/-- THE ARM INVARIANT (`arm_preserves_vm`): the arm's checker leaves
    `vm_wf` alone.  Stated over the `ca_check` FIELD rather than over a named
    checker, so it can be a `Forall` over `checked_table` — the table holds
    records, and the record's field is what `check_syscall` calls. -/
def arm_preserves_vm (c : CheckedArm) : Prop :=
  ∀ (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event),
    c.ca_check i eff m = .CheckOk m' evs →
    vm_wf (m_vmmaps m) → vm_wf (m_vmmaps m')

/- The per-arm lemmas, in `checked_table`'s own order.  Each is

     intro i eff m m' evs H Hwf
     simp only [arm_X] at H          -- the arm record, a TERM-level equation
     rw [check_X_frame … H]          -- the frame: m_vmmaps m' = m_vmmaps m
     exact Hwf

   which is `check_brk_preserves`'s shape (see `Core.lean`).  The frame's
   word-argument positions are left to unification: every one of them occurs
   in `H`'s statement, so `(eff := …) (m := …)` names all that is needed and
   the arguments are recovered by the same defeq that makes the arm a lambda
   around its checker. -/

/-- `getcwd`. -/
theorem arm_getcwd_preserves_vm : arm_preserves_vm arm_getcwd := by
  intro i eff m m' evs H Hwf
  simp only [arm_getcwd] at H
  rw [check_getcwd_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `eventfd2`. -/
theorem arm_eventfd2_preserves_vm : arm_preserves_vm arm_eventfd2 := by
  intro i eff m m' evs H Hwf
  simp only [arm_eventfd2] at H
  rw [check_eventfd2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `epoll_create1`. -/
theorem arm_epoll_create1_preserves_vm : arm_preserves_vm arm_epoll_create1 := by
  intro i eff m m' evs H Hwf
  simp only [arm_epoll_create1] at H
  rw [check_epoll_create1_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `epoll_ctl`. -/
theorem arm_epoll_ctl_preserves_vm : arm_preserves_vm arm_epoll_ctl := by
  intro i eff m m' evs H Hwf
  simp only [arm_epoll_ctl] at H
  rw [check_epoll_ctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `epoll_pwait`. -/
theorem arm_epoll_pwait_preserves_vm : arm_preserves_vm arm_epoll_pwait := by
  intro i eff m m' evs H Hwf
  simp only [arm_epoll_pwait] at H
  rw [check_epoll_pwait_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `dup`. -/
theorem arm_dup_preserves_vm : arm_preserves_vm arm_dup := by
  intro i eff m m' evs H Hwf
  simp only [arm_dup] at H
  rw [check_dup_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `dup3`. -/
theorem arm_dup3_preserves_vm : arm_preserves_vm arm_dup3 := by
  intro i eff m m' evs H Hwf
  simp only [arm_dup3] at H
  rw [check_dup3_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `fcntl`. -/
theorem arm_fcntl_preserves_vm : arm_preserves_vm arm_fcntl := by
  intro i eff m m' evs H Hwf
  simp only [arm_fcntl] at H
  rw [check_fcntl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `ioctl`. -/
theorem arm_ioctl_preserves_vm : arm_preserves_vm arm_ioctl := by
  intro i eff m m' evs H Hwf
  simp only [arm_ioctl] at H
  rw [check_ioctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `flock`. -/
theorem arm_flock_preserves_vm : arm_preserves_vm arm_flock := by
  intro i eff m m' evs H Hwf
  simp only [arm_flock] at H
  rw [check_flock_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `unlinkat`. -/
theorem arm_unlinkat_preserves_vm : arm_preserves_vm arm_unlinkat := by
  intro i eff m m' evs H Hwf
  simp only [arm_unlinkat] at H
  rw [check_unlinkat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `ftruncate`. -/
theorem arm_ftruncate_preserves_vm : arm_preserves_vm arm_ftruncate := by
  intro i eff m m' evs H Hwf
  simp only [arm_ftruncate] at H
  rw [check_ftruncate_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `faccessat`. -/
theorem arm_faccessat_preserves_vm : arm_preserves_vm arm_faccessat := by
  intro i eff m m' evs H Hwf
  simp only [arm_faccessat] at H
  rw [check_faccessat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `openat`. -/
theorem arm_openat_preserves_vm : arm_preserves_vm arm_openat := by
  intro i eff m m' evs H Hwf
  simp only [arm_openat] at H
  rw [check_openat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `close`. -/
theorem arm_close_preserves_vm : arm_preserves_vm arm_close := by
  intro i eff m m' evs H Hwf
  simp only [arm_close] at H
  rw [check_close_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `pipe2`. -/
theorem arm_pipe2_preserves_vm : arm_preserves_vm arm_pipe2 := by
  intro i eff m m' evs H Hwf
  simp only [arm_pipe2] at H
  rw [check_pipe2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getdents64`. -/
theorem arm_getdents64_preserves_vm : arm_preserves_vm arm_getdents64 := by
  intro i eff m m' evs H Hwf
  simp only [arm_getdents64] at H
  rw [check_getdents64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `lseek`. -/
theorem arm_lseek_preserves_vm : arm_preserves_vm arm_lseek := by
  intro i eff m m' evs H Hwf
  simp only [arm_lseek] at H
  rw [check_lseek_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `read`. -/
theorem arm_read_preserves_vm : arm_preserves_vm arm_read := by
  intro i eff m m' evs H Hwf
  simp only [arm_read] at H
  rw [check_read_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `write`. -/
theorem arm_write_preserves_vm : arm_preserves_vm arm_write := by
  intro i eff m m' evs H Hwf
  simp only [arm_write] at H
  rw [check_write_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `readv`. -/
theorem arm_readv_preserves_vm : arm_preserves_vm arm_readv := by
  intro i eff m m' evs H Hwf
  simp only [arm_readv] at H
  rw [check_readv_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `writev`. -/
theorem arm_writev_preserves_vm : arm_preserves_vm arm_writev := by
  intro i eff m m' evs H Hwf
  simp only [arm_writev] at H
  rw [check_writev_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `pread64`. -/
theorem arm_pread64_preserves_vm : arm_preserves_vm arm_pread64 := by
  intro i eff m m' evs H Hwf
  simp only [arm_pread64] at H
  rw [check_pread64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `pwrite64`. -/
theorem arm_pwrite64_preserves_vm : arm_preserves_vm arm_pwrite64 := by
  intro i eff m m' evs H Hwf
  simp only [arm_pwrite64] at H
  rw [check_pwrite64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `pselect6`. -/
theorem arm_pselect6_preserves_vm : arm_preserves_vm arm_pselect6 := by
  intro i eff m m' evs H Hwf
  simp only [arm_pselect6] at H
  rw [check_pselect6_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `ppoll`. -/
theorem arm_ppoll_preserves_vm : arm_preserves_vm arm_ppoll := by
  intro i eff m m' evs H Hwf
  simp only [arm_ppoll] at H
  rw [check_ppoll_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `readlinkat`. -/
theorem arm_readlinkat_preserves_vm : arm_preserves_vm arm_readlinkat := by
  intro i eff m m' evs H Hwf
  simp only [arm_readlinkat] at H
  rw [check_readlinkat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `newfstatat`. -/
theorem arm_newfstatat_preserves_vm : arm_preserves_vm arm_newfstatat := by
  intro i eff m m' evs H Hwf
  simp only [arm_newfstatat] at H
  rw [check_newfstatat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `fstat`. -/
theorem arm_fstat_preserves_vm : arm_preserves_vm arm_fstat := by
  intro i eff m m' evs H Hwf
  simp only [arm_fstat] at H
  rw [check_fstat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `fsync`. -/
theorem arm_fsync_preserves_vm : arm_preserves_vm arm_fsync := by
  intro i eff m m' evs H Hwf
  simp only [arm_fsync] at H
  rw [check_fsync_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `fdatasync`. -/
theorem arm_fdatasync_preserves_vm : arm_preserves_vm arm_fdatasync := by
  intro i eff m m' evs H Hwf
  simp only [arm_fdatasync] at H
  rw [check_fsync_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `timerfd_create`. -/
theorem arm_timerfd_create_preserves_vm : arm_preserves_vm arm_timerfd_create := by
  intro i eff m m' evs H Hwf
  simp only [arm_timerfd_create] at H
  rw [check_timerfd_create_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `exit`. -/
theorem arm_exit_preserves_vm : arm_preserves_vm arm_exit := by
  intro i eff m m' evs H Hwf
  simp only [arm_exit] at H
  rw [check_exit_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `exit_group`. -/
theorem arm_exit_group_preserves_vm : arm_preserves_vm arm_exit_group := by
  intro i eff m m' evs H Hwf
  simp only [arm_exit_group] at H
  rw [check_exit_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `set_tid_address`. -/
theorem arm_set_tid_address_preserves_vm : arm_preserves_vm arm_set_tid_address := by
  intro i eff m m' evs H Hwf
  simp only [arm_set_tid_address] at H
  rw [check_set_tid_address_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `futex`. -/
theorem arm_futex_preserves_vm : arm_preserves_vm arm_futex := by
  intro i eff m m' evs H Hwf
  simp only [arm_futex] at H
  rw [check_futex_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `nanosleep`. -/
theorem arm_nanosleep_preserves_vm : arm_preserves_vm arm_nanosleep := by
  intro i eff m m' evs H Hwf
  simp only [arm_nanosleep] at H
  rw [check_nanosleep_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `clock_gettime`. -/
theorem arm_clock_gettime_preserves_vm : arm_preserves_vm arm_clock_gettime := by
  intro i eff m m' evs H Hwf
  simp only [arm_clock_gettime] at H
  rw [check_clock_gettime_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `sched_setscheduler`. -/
theorem arm_sched_setscheduler_preserves_vm : arm_preserves_vm arm_sched_setscheduler := by
  intro i eff m m' evs H Hwf
  simp only [arm_sched_setscheduler] at H
  rw [check_sched_setscheduler_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `sched_getaffinity`. -/
theorem arm_sched_getaffinity_preserves_vm : arm_preserves_vm arm_sched_getaffinity := by
  intro i eff m m' evs H Hwf
  simp only [arm_sched_getaffinity] at H
  rw [check_sched_getaffinity_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `sched_yield`. -/
theorem arm_sched_yield_preserves_vm : arm_preserves_vm arm_sched_yield := by
  intro i eff m m' evs H Hwf
  simp only [arm_sched_yield] at H
  rw [check_sched_yield_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `tkill`. -/
theorem arm_tkill_preserves_vm : arm_preserves_vm arm_tkill := by
  intro i eff m m' evs H Hwf
  simp only [arm_tkill] at H
  rw [check_tkill_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `tgkill`. -/
theorem arm_tgkill_preserves_vm : arm_preserves_vm arm_tgkill := by
  intro i eff m m' evs H Hwf
  simp only [arm_tgkill] at H
  rw [check_tgkill_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `sigaltstack`. -/
theorem arm_sigaltstack_preserves_vm : arm_preserves_vm arm_sigaltstack := by
  intro i eff m m' evs H Hwf
  simp only [arm_sigaltstack] at H
  rw [check_sigaltstack_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `rt_sigaction`. -/
theorem arm_rt_sigaction_preserves_vm : arm_preserves_vm arm_rt_sigaction := by
  intro i eff m m' evs H Hwf
  simp only [arm_rt_sigaction] at H
  rw [check_rt_sigaction_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `rt_sigprocmask`. -/
theorem arm_rt_sigprocmask_preserves_vm : arm_preserves_vm arm_rt_sigprocmask := by
  intro i eff m m' evs H Hwf
  simp only [arm_rt_sigprocmask] at H
  rw [check_rt_sigprocmask_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `setgid`. -/
theorem arm_setgid_preserves_vm : arm_preserves_vm arm_setgid := by
  intro i eff m m' evs H Hwf
  simp only [arm_setgid] at H
  rw [check_setid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `setuid`. -/
theorem arm_setuid_preserves_vm : arm_preserves_vm arm_setuid := by
  intro i eff m m' evs H Hwf
  simp only [arm_setuid] at H
  rw [check_setid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `setresuid`. -/
theorem arm_setresuid_preserves_vm : arm_preserves_vm arm_setresuid := by
  intro i eff m m' evs H Hwf
  simp only [arm_setresuid] at H
  rw [check_setresid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `setresgid`. -/
theorem arm_setresgid_preserves_vm : arm_preserves_vm arm_setresgid := by
  intro i eff m m' evs H Hwf
  simp only [arm_setresgid] at H
  rw [check_setresid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `setsid`. -/
theorem arm_setsid_preserves_vm : arm_preserves_vm arm_setsid := by
  intro i eff m m' evs H Hwf
  simp only [arm_setsid] at H
  rw [check_setsid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getgroups`. -/
theorem arm_getgroups_preserves_vm : arm_preserves_vm arm_getgroups := by
  intro i eff m m' evs H Hwf
  simp only [arm_getgroups] at H
  rw [check_getgroups_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `setgroups`. -/
theorem arm_setgroups_preserves_vm : arm_preserves_vm arm_setgroups := by
  intro i eff m m' evs H Hwf
  simp only [arm_setgroups] at H
  rw [check_setgroups_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `uname`. -/
theorem arm_uname_preserves_vm : arm_preserves_vm arm_uname := by
  intro i eff m m' evs H Hwf
  simp only [arm_uname] at H
  rw [check_uname_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `prctl`. -/
theorem arm_prctl_preserves_vm : arm_preserves_vm arm_prctl := by
  intro i eff m m' evs H Hwf
  simp only [arm_prctl] at H
  rw [check_prctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `gettimeofday`. -/
theorem arm_gettimeofday_preserves_vm : arm_preserves_vm arm_gettimeofday := by
  intro i eff m m' evs H Hwf
  simp only [arm_gettimeofday] at H
  rw [check_gettimeofday_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getpid`. -/
theorem arm_getpid_preserves_vm : arm_preserves_vm arm_getpid := by
  intro i eff m m' evs H Hwf
  simp only [arm_getpid] at H
  rw [check_getpid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getuid`. -/
theorem arm_getuid_preserves_vm : arm_preserves_vm arm_getuid := by
  intro i eff m m' evs H Hwf
  simp only [arm_getuid] at H
  rw [check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `geteuid`. -/
theorem arm_geteuid_preserves_vm : arm_preserves_vm arm_geteuid := by
  intro i eff m m' evs H Hwf
  simp only [arm_geteuid] at H
  rw [check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getgid`. -/
theorem arm_getgid_preserves_vm : arm_preserves_vm arm_getgid := by
  intro i eff m m' evs H Hwf
  simp only [arm_getgid] at H
  rw [check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getegid`. -/
theorem arm_getegid_preserves_vm : arm_preserves_vm arm_getegid := by
  intro i eff m m' evs H Hwf
  simp only [arm_getegid] at H
  rw [check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `gettid`. -/
theorem arm_gettid_preserves_vm : arm_preserves_vm arm_gettid := by
  intro i eff m m' evs H Hwf
  simp only [arm_gettid] at H
  rw [check_gettid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `socket`. -/
theorem arm_socket_preserves_vm : arm_preserves_vm arm_socket := by
  intro i eff m m' evs H Hwf
  simp only [arm_socket] at H
  rw [check_socket_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `socketpair`. -/
theorem arm_socketpair_preserves_vm : arm_preserves_vm arm_socketpair := by
  intro i eff m m' evs H Hwf
  simp only [arm_socketpair] at H
  rw [check_socketpair_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `bind`. -/
theorem arm_bind_preserves_vm : arm_preserves_vm arm_bind := by
  intro i eff m m' evs H Hwf
  simp only [arm_bind] at H
  rw [check_bind_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `listen`. -/
theorem arm_listen_preserves_vm : arm_preserves_vm arm_listen := by
  intro i eff m m' evs H Hwf
  simp only [arm_listen] at H
  rw [check_listen_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `accept`. -/
theorem arm_accept_preserves_vm : arm_preserves_vm arm_accept := by
  intro i eff m m' evs H Hwf
  simp only [arm_accept] at H
  rw [check_accept4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `connect`. -/
theorem arm_connect_preserves_vm : arm_preserves_vm arm_connect := by
  intro i eff m m' evs H Hwf
  simp only [arm_connect] at H
  rw [check_connect_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getsockname`. -/
theorem arm_getsockname_preserves_vm : arm_preserves_vm arm_getsockname := by
  intro i eff m m' evs H Hwf
  simp only [arm_getsockname] at H
  rw [check_getsockname_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getpeername`. -/
theorem arm_getpeername_preserves_vm : arm_preserves_vm arm_getpeername := by
  intro i eff m m' evs H Hwf
  simp only [arm_getpeername] at H
  rw [check_getpeername_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `sendto`. -/
theorem arm_sendto_preserves_vm : arm_preserves_vm arm_sendto := by
  intro i eff m m' evs H Hwf
  simp only [arm_sendto] at H
  rw [check_sendto_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `recvfrom`. -/
theorem arm_recvfrom_preserves_vm : arm_preserves_vm arm_recvfrom := by
  intro i eff m m' evs H Hwf
  simp only [arm_recvfrom] at H
  rw [check_recvfrom_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `setsockopt`. -/
theorem arm_setsockopt_preserves_vm : arm_preserves_vm arm_setsockopt := by
  intro i eff m m' evs H Hwf
  simp only [arm_setsockopt] at H
  rw [check_setsockopt_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getsockopt`. -/
theorem arm_getsockopt_preserves_vm : arm_preserves_vm arm_getsockopt := by
  intro i eff m m' evs H Hwf
  simp only [arm_getsockopt] at H
  rw [check_getsockopt_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `shutdown`. -/
theorem arm_shutdown_preserves_vm : arm_preserves_vm arm_shutdown := by
  intro i eff m m' evs H Hwf
  simp only [arm_shutdown] at H
  rw [check_shutdown_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `sendmsg`. -/
theorem arm_sendmsg_preserves_vm : arm_preserves_vm arm_sendmsg := by
  intro i eff m m' evs H Hwf
  simp only [arm_sendmsg] at H
  rw [check_sendmsg_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `recvmsg`. -/
theorem arm_recvmsg_preserves_vm : arm_preserves_vm arm_recvmsg := by
  intro i eff m m' evs H Hwf
  simp only [arm_recvmsg] at H
  rw [check_recvmsg_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `brk` — the one writer whose preservation is a PART 2 theorem
    (`check_brk_preserves`, beside `brk_grant_wf`). -/
theorem arm_brk_preserves_vm : arm_preserves_vm arm_brk := by
  intro i eff m m' evs H Hwf
  simp only [arm_brk] at H
  exact check_brk_preserves (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hwf := Hwf)

/-- `clone`. -/
theorem arm_clone_preserves_vm : arm_preserves_vm arm_clone := by
  intro i eff m m' evs H Hwf
  simp only [arm_clone] at H
  rw [check_clone_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `madvise`. -/
theorem arm_madvise_preserves_vm : arm_preserves_vm arm_madvise := by
  intro i eff m m' evs H Hwf
  simp only [arm_madvise] at H
  rw [check_madvise_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `accept4`. -/
theorem arm_accept4_preserves_vm : arm_preserves_vm arm_accept4 := by
  intro i eff m m' evs H Hwf
  simp only [arm_accept4] at H
  rw [check_accept4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `wait4`. -/
theorem arm_wait4_preserves_vm : arm_preserves_vm arm_wait4 := by
  intro i eff m m' evs H Hwf
  simp only [arm_wait4] at H
  rw [check_wait4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `prlimit64`. -/
theorem arm_prlimit64_preserves_vm : arm_preserves_vm arm_prlimit64 := by
  intro i eff m m' evs H Hwf
  simp only [arm_prlimit64] at H
  rw [check_prlimit64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `getrandom`. -/
theorem arm_getrandom_preserves_vm : arm_preserves_vm arm_getrandom := by
  intro i eff m m' evs H Hwf
  simp only [arm_getrandom] at H
  rw [check_getrandom_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `clone3`. -/
theorem arm_clone3_preserves_vm : arm_preserves_vm arm_clone3 := by
  intro i eff m m' evs H Hwf
  simp only [arm_clone3] at H
  rw [check_clone3_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

/-- `faccessat2`. -/
theorem arm_faccessat2_preserves_vm : arm_preserves_vm arm_faccessat2 := by
  intro i eff m m' evs H Hwf
  simp only [arm_faccessat2] at H
  rw [check_faccessat2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)]
  exact Hwf

end LinuxSem.Checks.VmMapsDisjoint
