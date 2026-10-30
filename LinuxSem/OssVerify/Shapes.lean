/-
  * OssVerify.Shapes — what a statement about a compiled fuzz target says

  TRUST BOUNDARY: part of the statement layer.

  A statement is one of the definitions below, applied to the memory images of
  specific binaries.  Each is written out in full and proved EQUAL, by `rfl`, to
  the model definition it stands for, so what is read here is exactly what the
  model means.

  ** Vocabulary

  - IMAGE (`MemImageType.Image`): what the Linux loader maps from a static riscv64
    ELF file.
  - ENTRY (`Run.ExecEntry`): what the kernel chooses at execve and the program does
    not control: stack top, program break, mmap base, the AT_RANDOM bytes.
  - INPUT (`State.ProcInput`): everything the environment supplies: argv, envp, the
    file system, stdin, ids, network peers, limits, machine capabilities.
  - ERROR: a step the model does not interpret, or a fault it treats as one: an
    unmodelled system call or instruction, an invalid memory access, an illegal
    instruction (how a trapping UBSan check fails), and abort() (how a failed
    assert() and an AddressSanitizer report end the process).
-/
import LinuxSem.EquivalenceDefinition.HaltsAllowed

set_option autoImplicit false

open LinuxSem.Riscv

namespace LinuxSem.OssVerify.Shapes

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.HaltsAllowed
open behavior

/-- 16 GiB for the plain build, 512 GiB for the sanitizer build. -/
def budgets : BUDGETS := ShippedBudgets

theorem budgets_are : budgets.lim_source = 0x400000000 ∧ budgets.lim_target = 0x8000000000 :=
  ⟨rfl, rfl⟩

/-- 0 (the harness returned normally) or 2 (the driver refused the input).  An
    abort is not an exit at all. -/
def ok_or_refused : List word := [BitVec.ofInt 64 0, BitVec.ofInt 64 2]

/-- A sanitizer build agrees with the plain build: on every valid input and pair of
    entries on which the plain build is never refused memory for exceeding
    `lim_plain`, neither build reaches an error (so the sanitizer never reports) and
    the two have the same finite traces.  The environment may refuse any call.  The
    premise is on the plain build only: the sanitizer build gets no exemption. -/
def agrees (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp →
    valid_entry san en_san inp →
    valid_input inp →
    ¬ run_budget_refused plain lim_plain en_plain inp →
    error_free (run plain lim_plain en_plain inp)
    ∧ error_free (run san lim_san en_san inp)
    ∧ trace_equiv (bh_traces (run plain lim_plain en_plain inp))
                  (bh_traces (run san lim_san en_san inp))

theorem agrees_is_lps (lp ls : Int) (p s : Image) :
    agrees lp ls p s = strong_universal_error_free_T_budgets lp ls p s := rfl

/-- On every valid input and entry on which the run is never refused memory for
    exceeding `lim`, and when the environment refuses nothing it is not forced to,
    EVERY execution ends in exit_group with a status in `allowed`.  So none runs
    forever (the predicate is inductive), gets stuck, reaches an error, or dies by
    a signal.  Nothing is said about output. -/
def halts_within_budget (lim : Int) (allowed : List word) (img : Image) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput),
    valid_entry img en inp →
    valid_input inp →
    ¬ run_scfg_budget_refused forced_only_cfg img lim en inp →
    must_exit_in_scfg forced_only_cfg allowed img lim en inp

theorem halts_within_budget_is_lps (lim : Int) (allowed : List word) (img : Image) :
    halts_within_budget lim allowed img
    = halts_allowed_T_scfg_budgets forced_only_cfg lim allowed img := rfl

/-- As above with no budget premise, whatever the environment refuses, at the
    model's single-binary budget (16 GiB).  False for any build whose start-up waits
    forever when a reservation is refused, as an AddressSanitizer build's does. -/
def halts_may_fail (allowed : List word) (img : Image) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput),
    valid_entry img en inp →
    valid_input inp →
    must_exit_in_scfg may_fail_cfg allowed img source_alloc_limit en inp

theorem halts_may_fail_is_lps (allowed : List word) (img : Image) :
    halts_may_fail allowed img = halts_allowed_T_scfg may_fail_cfg allowed img := rfl

end LinuxSem.OssVerify.Shapes
