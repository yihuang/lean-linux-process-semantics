/-
  * LinuxSem.Checks.Omni — what the omni judgments MEAN

  Not part of the trusted specification: QA on the definitions of
  `OmniRun` and `OmniEquivalence`, in the style of `Checks/Examples`.
  Every case here is UNIVERSALLY QUANTIFIED (admission reason 1 of that
  file: a `forall` over every execution of a run, which no finite set of
  traces establishes) or COMPARES TWO RUNS (reason 2).

  - PART 1, the two coinductive readings agree on THIS tree.
    `OmniRun.coexec` drops the progress premise so that a stuck
    configuration reads as silent; `sstep_receptive` lifts
    `Checks.Progress.receptive` to `Run.sstep` and shows no non-halted
    configuration is stuck, so `coexec_progress_iff` identifies the
    two judgments here.  The header of `OmniRun` says why the choice
    is nevertheless made at the definition.
  - PART 2, the exit-0 image SATISFIES the omni statements, for EVERY
    `execve` placement, EVERY input and ANY budget: one omni
    induction (`exits_c_exec`) delivers the exact trace, termination
    and error-freedom at once, which is what
    `exit0_omni_strong_universal` — the first
    `OmniEquivalence.omni_strong_universal_T` any concrete pair
    satisfies — is made of.  The legacy
    `Equivalence.strong_universal_T` follows through the `iff`, and the
    module ascriptions at the end of the part show the two checker
    shapes accepting the same proof.
  - PART 3, the undecodable image REFUTES them: every error-related
    omni postcondition fails on it, the identical-pair statement
    fails with it as the source, and the differing pair
    exit-0/undecodable fails through the trace conjunct.
  - PART 4, a modeled CRASH separates the three error postconditions:
    an `ebreak` image satisfies `OmniRun.errors` and `OmniRun.covered`
    and refutes `OmniRun.never_errors`, and its escape frees any
    target — the `OmniEquivalence.omni_strong_equiv` of a crashing
    source against the undecodable image holds.
  - PART 5, `exec`/`coexec` agreement is STRICTLY WEAKER than trace
    equivalence: "write one byte, then loop" and "loop" satisfy the
    same `coexec` postconditions (every one) and the same `exec`
    postconditions (none), yet their trace sets differ, so
    `OmniRun.cosafe` — and `Equivalence.equiv` through the `iff` —
    tells them apart.  This is `Checks.Examples.write_then_diverge_vs_diverge`
    on two real images, and the reason trace equivalence is stated on
    the prefix judgment.

  ** Computing on a machine state without reading it back

  Every fact below that is closed by computation is a SCALAR: a
  boolean, a byte list, a checker verdict.  A machine state is never
  normalised into a goal — its stack memory is a closure over the
  initial stack image, and reading that closure back is where
  computation runs out of memory (the same trap
  `Common/StepTac` guards against).  Where a lemma must name the
  successor STATE, the memory field is abstracted first: `with_mem`
  replaces it by a variable, `with_mem_eta` says nothing is lost, and
  an instruction that touches no memory then steps
  `with_mem ms mem` to `with_mem ms' mem` by computation on the
  remaining fields alone.  The syscall step, which does read memory,
  is characterised through
  `Checks.Cases.Fs.ReadWrite.write_channel_outcome`
  and the executable checker, both on the real memory.

  ** Contents, part by part

  This file's extra `theorem`/`def` declarations are local helpers,
  named so that they cannot be mistaken for specification:
  `wloop_*`/`check_write_wloop_*`/`with_mem_ms_pc` (PART 5's staged
  evaluator), `with_mem`/`no_lazy*`/`istep` (the memory abstraction), and
  `sstep_exit_only` (PART 2's exit-arm inversion).

  - PART 1, stated over `Run.sstep` alone;
  - PART 2, with `sstep_exit_only`: the engine `exits_c_exec` — the omni
    form of `Checks.Examples.exits_c_must_exit_at`; then `exit0_exits_c`,
    `exit0_exec`, `exit0_obs`,
    `exit0_never_errors`, the two universals
    (`exit0_omni_strong_universal`, `exit0_strong_universal`) with the
    three ascriptions (`Exit0Image`, `Exit0OmniChecked`, `Exit0Checked`),
    the whole abort stance family (`exit0_strong_equiv_any` …
    `exit0_error_free_run`, the four `*_error_free_*` universals, the four
    `*_scfg*` shapes and their six ascriptions), and the classifier-side
    examples (`exit0_omni_exits_zero`, `…_direct`, `…_legacy`, and
    `exit0_omni_not_exits_one`, the check that bites);
  - PART 3: every error postcondition refuted on
    the undecodable image, the two `omni_strong_universal_T` refutations,
    and `undecodable_cosafe_nil` — these need no `exits_c` walk at all,
    only `Checks.Examples`' `undecodable_step_unmodeled_at_demo_entry` and
    `unmodeled_no_next`;
  - PART 4: the `ebreak` fixtures and their instruction-level
    lemmas (`ebreak_segment` … `ebreak_only`) AND the omni statements
    (`ebreak_omni_errors`, `ebreak_omni_covered`,
    `ebreak_omni_not_never_errors`, `ebreak_omni_may_errors`,
    `ebreak_source_omni_strong_equiv_any`,
    `ebreak_frees_undecodable_target`, `ebreak_refutes_omni_error_free`);
  - PART 5: the `loop`/`wloop` pair, `run_steps`, the five
    instruction steps, the ecall (`wloop_write_forced`,
    `wloop_checker`, `wloop_syscall_sstep`, `wloop_syscall_only`), the
    fixpoint, and the four refutations
    (`loop_wloop_cosafe_disagree`, `loop_wloop_not_trace_equiv`,
    `loop_wloop_not_omni_equiv`, `loop_wloop_not_equiv`,
    `loop_wloop_refutes_omni_strong_universal`) with the validity
    lemmas that make them refutations at a VALID triple.

  The ecall needed a per-arm staged evaluator, because no single recipe
  closes every arm.  `check_write_wloop_walk` folds
  the CHANNEL arm of `Checks.Sys.Fs.ReadWrite.check_write` past every
  argument gate at this input (the descriptor is stdout, the count gate
  passes, the moved byte is the image's own `0x93`), which leaves the
  claimed-effect test alone; `check_write_wloop_inv` then reads the two
  surviving tests, and `Checks.Sys.DispatchCompute.check_syscall_write`
  carries it from the checker to `syscall_spec`.  The step inversion
  itself reuses `Common/Nodes.lean`'s `sstep_svc_inv` — `Checks` has
  no `sstep` inversion of its own, and that one is phrased through the
  checker, which is exactly what the walk pins.

  ** Order — `fix_star_nil` comes first

  `fix_coexec_any` would be a `cofix` over a coinductive judgment and
  need no star analysis at all.  `OmniRun.coexec` is instead the
  FINITE-UNROLLING LIMIT — a `∀ tr c', star … → …` — so the same fact is a
  computation over `Run.star`, and `fix_coexec_any` needs `fix_star_nil`
  before it.  The four `fix_*` lemmas are therefore in the order
  `fix_star_nil`, `fix_obs_nil`, `fix_coexec_any`, `fix_no_exec`; the
  statements are unchanged.

  ** Spelling

  `Z` is `Int`; `bv n`/`word`/`byte` are `BitVec n`/`BitVec 64`/`BitVec 8`;
  `Z_to_bv n z` is `BitVec.ofInt n z`; `bv_unsigned a` is `(a.toNat : Int)`;
  `mkCfg` is the `config` constructor; `Ok`/`Unmodeled` are
  `.ok`/`.unmodeled`; `MachineOk`/`MachineFault`/`MachineUnmodeled` are
  the `machine_result` constructors of the same names; `SNext`/`SError`
  are `step_to.SNext`/`.SError`; `N` is `Nat`.  `inversion Hss`
  over the seven `sstep` constructors is a `cases`, and the three
  `no_lazy*` steps are `macro`s of the same name.
-/
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.Checks.Progress
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.Classifier
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Checks.Examples
import LinuxSem.Checks.Sys.DispatchCompute
import LinuxSem.Common.Nodes

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.Checks.Progress
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Examples (demo_entry exit0_segments exit0_image
  undecodable_image demo_input_valid)
open LinuxSem.Checks.ExecutableSpecs (check_syscall check_syscall_ok_iff
  check_syscall_complete_ok check_syscall_complete_unmodeled)
open LinuxSem.Checks.Sys.Fs.ReadWrite (check_write)
open LinuxSem.Checks.Sys.DispatchCompute (check_syscall_write)
open LinuxSem.Common.Nodes (sstep_svc_inv halt_ev)
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.EquivalenceDefinition.Equivalence (run_all_errors_errors)
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uaccess

namespace LinuxSem.Checks.Omni

/-! The process input every concrete pin below runs on — the one
    `Checks.Examples.demo_input_valid` validates: one empty argument,
    no environment, an empty file system, end of input. -/
def demo_proc_input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (BitVec.ofInt 64 0) demo_hwcap false .Sv48

/- =========================================================================
   PART 1 — receptiveness lifted to `Run.sstep`
   ========================================================================= -/

/-- No non-halted configuration is stuck: an instruction step answers
    one of `MachineOk`/`MachineFault`/`MachineUnmodeled`, each with an
    `sstep` constructor, and a pending syscall admits some outcome by
    `Checks.Progress.receptive`, each shape of which again has one. -/
theorem sstep_receptive (segs : List Segment) (c : config)
    (Hh : m_halted c.cfg_model = none) : ∃ evs st, sstep segs c evs st := by
  obtain ⟨ms, model⟩ := c
  cases hsvc : ms.ms_svc_pending with
  | none =>
    -- the witness outcome, with its name generalised so that the case
    -- split rewrites the receptiveness fact itself
    cases hacc : mi_account_step segs ms model with
    | MachineOk p =>
      obtain ⟨ms', model'⟩ := p
      exact ⟨[], .SNext ⟨ms', model'⟩, sstep.instr ms model ms' model' Hh hsvc hacc⟩
    | MachineFault =>
      exact ⟨[], .SError, sstep.instr_fault ms model Hh hsvc hacc⟩
    | MachineUnmodeled =>
      exact ⟨[], .SError, sstep.instr_unmodeled ms model Hh hsvc hacc⟩
  | some x8 =>
    obtain hrec := receptive (sys_input segs ms x8) model
    cases hw : syscall_spec_witness (sys_input segs ms x8) model with
    | ok eff model' evs => 
      rw [hw] at hrec
      cases hh' : m_halted model' with
      | some code =>
        cases hk : m_killed model' with
        | some sig =>
          exact ⟨_, _, sstep.killed ms model x8 eff model' evs sig Hh hsvc hrec hk⟩
        | none =>
          exact ⟨_, _, sstep.exit ms model x8 eff model' evs code Hh hsvc hrec hh' hk⟩
      | none =>
        cases hmat : materialize_model_accesses model'
            (syscall_effect_accesses eff) with
        | some model'' =>
          exact ⟨_, _, sstep.syscall ms model x8 eff model' model'' evs Hh hsvc hrec hh' hmat⟩
        | none =>
          exact ⟨_, _, sstep.syscall_materialization_fault ms model x8 eff model' evs
                   Hh hsvc hrec hh' hmat⟩
    | unmodeled =>
      rw [hw] at hrec
      exact ⟨_, _, sstep.syscall_unmodeled ms model x8 Hh hsvc hrec⟩

/-- Hence the progress-carrying variant is no stronger here. -/
theorem coexec_coexec_progress (segs : List Segment) (c : config) (Q : post)
    (H : coexec segs c Q) : coexec_progress segs c Q := by
  -- `OmniRun.coexec_progress` is `coexec ∧` the progress clause, so the
  -- second component is all there is to show, and
  -- `sstep_receptive` at an arbitrary `star` successor is the whole proof.
  refine ⟨H, ?_⟩
  intro tr c' _ Hh
  exact sstep_receptive segs c' Hh

theorem coexec_progress_iff (segs : List Segment) (c : config) (Q : post) :
    coexec segs c Q ↔ coexec_progress segs c Q :=
  ⟨coexec_coexec_progress segs c Q, coexec_progress_implies segs c Q⟩

/- =========================================================================
   Machine states with the memory abstracted
   ========================================================================= -/

def with_mem (ms : machine_state) (mem : word → Option byte) : machine_state :=
  { ms_regs := ms.ms_regs, ms_fregs := ms.ms_fregs, ms_pc_val := ms.ms_pc_val,
    ms_svc_pending := ms.ms_svc_pending, ms_resv := ms.ms_resv,
    ms_fcsr := ms.ms_fcsr, ms_mem := mem, ms_rom := ms.ms_rom }

theorem with_mem_eta (ms : machine_state) : ms = with_mem ms ms.ms_mem := by
  cases ms
  rfl

/-- Erase the accounting on a model with no lazy mappings, in the goal
    or in a hypothesis; the model is read off the term, so the `rfl`
    that discharges `m_vm_lazy model = []` sees it. -/
macro "no_lazy" : tactic =>
  `(tactic| first
    | rw [mi_account_step_no_lazy _ _ _ (by rfl)]
    | rw [mi_account_step_no_lazy _ _ _ (by decide)])

macro "no_lazy_in " h:ident : tactic =>
  `(tactic| first
    | rw [mi_account_step_no_lazy _ _ _ (by rfl)] at $h:ident
    | rw [mi_account_step_no_lazy _ _ _ (by decide)] at $h:ident)

macro "no_lazy_materialize_in " h:ident : tactic =>
  `(tactic| first
    | rw [materialize_model_accesses_no_lazy _ _ (by rfl)] at $h:ident
    | rw [materialize_model_accesses_no_lazy _ _ (by decide)] at $h:ident)

/-! The macros' one use shape, pinned so that it is exercised: the model
    is read off the term, so the `rfl` inside them discharges the side
    condition. -/
example (segs : List Segment) (ms : machine_state) (inp : ProcInput) (z : Int) :
    mi_account_step segs ms (init_model [] 0 0 demo_sp z inp) =
      (match RiscvSemantics.step segs ms with
       | .MachineOk ms' => .MachineOk (ms', init_model [] 0 0 demo_sp z inp)
       | .MachineFault => .MachineFault
       | .MachineUnmodeled => .MachineUnmodeled) := by
  no_lazy
  rfl

/-- From a configuration whose instruction step is a function answer,
    the only transition is that step, silently.  The same fact as
    `Common/ExitSim`'s `sstep_instr_inv`, restated here because
    `Common` is not part of the package. -/
theorem sstep_instr_only (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms') :
    ∀ evs st, sstep segs ⟨ms, model⟩ evs st → evs = [] ∧ st = .SNext ⟨ms', model⟩ := by
  intro evs st hss
  cases hss with
  | instr ms0 model0 ms0' model0' hh hsvc0 hstep =>
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
    simp only [machine_result.MachineOk.injEq, Prod.mk.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨rfl, rfl⟩
  | instr_fault ms0 model0 hh hsvc0 hstep =>
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
    exact absurd hstep (by simp)
  | instr_unmodeled ms0 model0 hh hsvc0 hstep =>
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
    exact absurd hstep (by simp)
  | syscall ms0 model0 x8 eff model' model'' evs0 hh hsvc0 _ _ _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)
  | syscall_materialization_fault ms0 model0 x8 eff model' evs0 hh hsvc0 _ _ _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)
  | exit ms0 model0 x8 eff model' evs0 code hh hsvc0 _ _ _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)
  | killed ms0 model0 x8 eff model' evs0 sig hh hsvc0 _ _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)
  | syscall_unmodeled ms0 model0 x8 hh hsvc0 _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)

/-- ... and when the answer is a fault, the only transition is the
    error one. -/
theorem sstep_fault_only (segs : List Segment) (ms : machine_state) (model : Model)
    (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineFault) :
    ∀ evs st, sstep segs ⟨ms, model⟩ evs st → evs = [] ∧ st = .SError := by
  intro evs st hss
  cases hss with
  | instr ms0 model0 ms0' model0' hh hsvc0 hstep =>
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
    exact absurd hstep (by simp)
  | instr_fault ms0 model0 hh hsvc0 hstep =>
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
    exact ⟨rfl, rfl⟩
  | instr_unmodeled ms0 model0 hh hsvc0 hstep =>
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
    exact absurd hstep (by simp)
  | syscall ms0 model0 x8 eff model' model'' evs0 hh hsvc0 _ _ _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)
  | syscall_materialization_fault ms0 model0 x8 eff model' evs0 hh hsvc0 _ _ _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)
  | exit ms0 model0 x8 eff model' evs0 code hh hsvc0 _ _ _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)
  | killed ms0 model0 x8 eff model' evs0 sig hh hsvc0 _ _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)
  | syscall_unmodeled ms0 model0 x8 hh hsvc0 _ =>
    rw [Hsvc] at hsvc0
    exact absurd hsvc0 (by simp)

/-- CRITICAL DEPENDENCY of `Run.obs_trace`'s coinductive reading: a
    configuration that always steps to itself is silent forever.  Stated
    first, because `coexec` here is the finite-unrolling limit and
    the three `fix_*` lemmas below all read the star analysis off it. -/
theorem fix_star_nil (segs : List Segment) (c : config)
    (Hfix : ∀ evs st, sstep segs c evs st → evs = [] ∧ st = .SNext c) :
    ∀ tr c', star segs c tr c' → tr = [] ∧ c' = c := by
  have key : ∀ (c0 : config) (tr : List event) (c' : config),
      star segs c0 tr c' → c0 = c → tr = [] ∧ c' = c := by
    intro c0 tr c' hstar
    induction hstar with
    | refl c1 => intro hc; exact ⟨rfl, hc⟩
    | step c1 evs c2 tr c3 h1 h2 ih =>
      intro hc
      subst hc
      obtain ⟨hev, hc2⟩ := Hfix evs (.SNext c2) h1
      obtain rfl : c2 = c1 := by injection hc2
      obtain ⟨htr, hc3⟩ := ih rfl
      exact ⟨by rw [hev, htr]; rfl, hc3⟩
  intro tr c' hstar
  exact key c tr c' hstar rfl

theorem fix_obs_nil (segs : List Segment) (c : config)
    (Hfix : ∀ evs st, sstep segs c evs st → evs = [] ∧ st = .SNext c) :
    ∀ tr, obs_trace segs c tr → tr = [] := by
  intro tr ⟨tr', c', hstar, hp⟩
  obtain ⟨rfl, -⟩ := fix_star_nil segs c Hfix tr' c' hstar
  cases tr with
  | nil => rfl
  | cons x xs => exact False.elim hp

/-- A configuration that steps to itself: silent forever. -/
theorem fix_coexec_any (segs : List Segment) (c : config)
    (Hh : m_halted c.cfg_model = none)
    (Hfix : ∀ evs st, sstep segs c evs st → evs = [] ∧ st = .SNext c) :
    ∀ Q, coexec segs c Q := by
  intro Q tr c' hstar
  obtain ⟨rfl, rfl⟩ := fix_star_nil segs c Hfix tr c' hstar
  refine ⟨?_, ?_⟩
  · intro hne
    exact absurd Hh hne
  · intro evs hss
    exact absurd (Hfix evs .SError hss).2 (by simp)

theorem fix_no_exec (segs : List Segment) (c : config)
    (Hh : m_halted c.cfg_model = none)
    (Hfix : ∀ evs st, sstep segs c evs st → evs = [] ∧ st = .SNext c) :
    ∀ Q, ¬ exec segs c Q := by
  intro Q Hex
  -- The induction goes over the star analysis of the `mexec` a
  -- terminating judgment realizes, not over the judgment itself, so it
  -- covers the two shapes a maximal execution can end in.
  obtain ⟨tr, o, hm, -⟩ := exec_realizes segs c Q Hex
  cases o with
  | OHalt c' =>
    obtain ⟨hstar, hh⟩ := mexec_halt_star segs c tr (.OHalt c') hm c' rfl
    obtain ⟨-, rfl⟩ := fix_star_nil segs c Hfix tr c' hstar
    exact absurd Hh hh
  | OError c' =>
    obtain ⟨tr1, evs, -, hstar, hss⟩ := mexec_error_star segs c tr (.OError c') hm c' rfl
    obtain ⟨-, rfl⟩ := fix_star_nil segs c Hfix tr1 c' hstar
    exact absurd (Hfix evs .SError hss).2 (by simp)

theorem prefix_closed_nil : prefix_closed (fun tr => tr = []) := by
  intro tr tr' h hp
  subst h
  cases tr' with
  | nil => rfl
  | cons x xs => exact False.elim hp


/- =========================================================================
   PART 2 — the omni form of `exits_c_must_exit_at`

   `Checks.Examples.exits_c_must_exit_at` walks `exits_c` to conclude
   `MustExit.must_exit_at`.  The omni judgment needs the SAME walk with the
   OBSERVATIONS recorded: the postcondition of `exec` sees the accumulated
   trace and how the execution ended, so a trace statement cannot be
   discharged from `must_exit_at` (which says nothing about the trace) and
   would need a second lemma relating the two.  `exits_c_exec` is that walk
   with the trace and the exit code recorded together, which is what makes
   every statement in PARTS 2 and 3 below a one-line consequence.

   The two walks share no code because they conclude different judgments,
   but they share every ingredient:

   - the ecall level is `sstep_exit_only`, the inversion
     `must_exit_at_exit_pending` performs, with the transition's SHAPE
     recorded instead of a `must_exit_at` conclusion: `exit_dispatch_forced`
     fixes the post-model, the event list (empty) and the emitted event, and
     `exit_dispatch_halts` / `exit_dispatch_not_killed` /
     `exit_dispatch_modeled` rule out the four other syscall arms;
   - the instruction level is `sstep_instr_only`, and `mi_account_step_no_lazy`
     keeps the model FIXED across it, so the induction hypothesis applies to
     the successor configuration unchanged.
   ========================================================================= -/

section Part2

open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.MustExit


/-- At a configuration whose pending syscall is an exit carrying `code`,
    the ONLY transition is the exit itself: it emits exactly the one exit
    event, with `code` and the pre-exit file system, and lands on the
    halted model — `m_halted = some code`, `m_killed = none`.

    This is `Verdicts.must_exit_at_exit_pending`'s inversion with the
    transition recorded, and it is what `exits_c_exec` needs twice: for the
    transition the walk takes, and for the claim that no other one exists. -/
theorem sstep_exit_only (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 code : word)
    (hsvc : ms.ms_svc_pending = some x8)
    (hno : Examples.exit_sysno (sys_input segs ms x8).in_sysno)
    (hcode : ms_gpr ms 0 &&& BitVec.ofInt 64 255 = code) :
    ∀ evs st, sstep segs ⟨ms, model⟩ evs st →
      ∃ m', st = .SNext ⟨ms, m'⟩ ∧ evs = [event.ExitEv code (m_fs model)] ∧
        m_halted m' = some code ∧ m_killed m' = none := by
  intro evs st hss
  cases hss with
  | instr ms0 model0 ms1 model1 hh0 hsvc0 hstep =>
      rw [hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | instr_fault ms0 model0 hh0 hsvc0 hstep =>
      rw [hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | instr_unmodeled ms0 model0 hh0 hsvc0 hstep =>
      rw [hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | syscall ms0 model0 x8' eff m' m'' evs hh0 hsvc0 hspec hh' hmat =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      rw [Examples.exit_dispatch_halts (sys_input segs ms x8) model eff m' evs hno hspec] at hh'
      exact absurd hh' (by simp)
  | syscall_materialization_fault ms0 model0 x8' eff m' evs hh0 hsvc0 hspec hh' hmat =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      rw [Examples.exit_dispatch_halts (sys_input segs ms x8) model eff m' evs hno hspec] at hh'
      exact absurd hh' (by simp)
  | exit ms0 model0 x8' eff m' evs0 code' hh0 hsvc0 hspec hh' hk =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      obtain ⟨-, hmod, hevs⟩ :=
        Examples.exit_dispatch_forced (sys_input segs ms x8) model eff m' evs0 hno hspec
      subst hmod
      subst hevs
      rw [m_halted_with_halted] at hh'
      have hsome : (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) = code' :=
        Option.some.inj hh'
      have hcode' : code' = code := by
        rw [← hsome,
          LinuxSem.Examples.PatchClassifyDemo.Verdicts.sys_input_arg0, hcode]
      refine ⟨with_halted (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) model,
        rfl, ?_, ?_, ?_⟩
      · rw [List.nil_append, m_fs_with_halted, hcode']
      · rw [m_halted_with_halted,
          LinuxSem.Examples.PatchClassifyDemo.Verdicts.sys_input_arg0, hcode]
      · rw [m_killed_with_halted]
  | killed ms0 model0 x8' eff m' evs0 sig hh0 hsvc0 hspec hk =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      rw [Examples.exit_dispatch_not_killed (sys_input segs ms x8) model eff m' evs0 hno hspec]
        at hk
      exact absurd hk (by simp)
  | syscall_unmodeled ms0 model0 x8' hh0 hsvc0 hspec =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      exact absurd hspec (Examples.exit_dispatch_modeled (sys_input segs ms x8) model hno)

/-- ** `exits_c` is sound for `OmniRun.exec`**: the reflective walk that
    `exits_c_must_exit_at` turns into `must_exit_at` also turns into the
    omni judgment, with the exact trace and the exit code in the
    postcondition.

    The conclusion is written with `⟨ms, model⟩` rather than
    `mkCfg ms model` (`mkCfg` is `Common/AsanAcct`'s abbreviation and is
    definitionally the constructor pair, as in
    `Checks.Examples.exits_c_must_exit_at`).

    The trace is `[ExitEv code (m_fs model)]` at the INITIAL model: the
    exit transition does not advance the machine state and `with_halted`
    leaves the file system alone, so the event's file system is the
    starting one — which is what makes trace equality at a run statement a
    computation rather than an induction over states.

    Both model premises are the same pair `exits_c_must_exit_at` needs, and
    both are `rfl` at an initial model (`m_halted_init_model`,
    `init_model_no_lazy`), so a consumer never instantiates the budget:
    `exit0_exec` below is `exits_c_exec` at every `execve` placement. -/
theorem exits_c_exec (segs : List Segment) (code : word) :
    ∀ (fuel : Nat) (ms : machine_state) (model : Model),
      m_halted model = none → m_vm_lazy model = [] →
      Examples.exits_c segs code fuel ms = true →
      exec segs ⟨ms, model⟩
        (fun tr o => tr = [event.ExitEv code (m_fs model)] ∧ exits_with code tr o) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ms model _ _ h
      simp only [Examples.exits_c,
        LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c] at h
      exact absurd h (by simp)
  | succ n ih =>
      intro ms model hh hlazy h
      cases hp : ms.ms_svc_pending with
      | some x8 =>
          -- the terminating ecall: the exit arm is the only transition
          have h' : ((decide ((x8.toNat : Int) = 93) || decide ((x8.toNat : Int) = 94))
              && ((ms_gpr ms 0 &&& BitVec.ofInt 64 255) == code)) = true := by
            simpa only [Examples.exits_c,
              LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c, hp] using h
          rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq,
            beq_iff_eq] at h'
          obtain ⟨hno, hcode⟩ := h'
          have hno' : Examples.exit_sysno (sys_input segs ms x8).in_sysno := by
            rcases hno with hno | hno
            · exact Or.inl hno
            · exact Or.inr hno
          have hstep : sstep segs ⟨ms, model⟩ [event.ExitEv code (m_fs model)]
              (.SNext ⟨ms, with_halted
                (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) model⟩) := by
            have h1 := sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
              (with_halted (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) model) []
              (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) hh hp
              (Examples.exit_dispatch_admits (sys_input segs ms x8) model hno')
              (by rw [m_halted_with_halted]) (by rw [m_killed_with_halted])
            simpa only [List.nil_append, m_fs_with_halted,
              LinuxSem.Examples.PatchClassifyDemo.Verdicts.sys_input_arg0,
              hcode] using h1
          refine exec.step ⟨ms, model⟩ _ hh ⟨_, _, hstep⟩ ?_ ?_
          · intro evs hss
            obtain ⟨m', hst, -, -, -⟩ :=
              sstep_exit_only segs ms model x8 code hp hno' hcode evs .SError hss
            cases hst
          · intro evs c' hss
            obtain ⟨m', hst, hevs, hhalt, hnk⟩ :=
              sstep_exit_only segs ms model x8 code hp hno' hcode evs (.SNext c') hss
            cases hst
            subst hevs
            refine exec.halt ⟨ms, m'⟩ _ (by rw [hhalt]; simp) ⟨?_, ?_⟩
            · rw [List.append_nil]
            · show m_halted m' = some code ∧ m_killed m' = none
              exact ⟨hhalt, hnk⟩
      | none =>
          -- an ordinary instruction: the accounted step is the bare step
          cases hstep : RiscvSemantics.step segs ms with
          | MachineOk ms' =>
              have hrec : Examples.exits_c segs code n ms' = true := by
                simp only [Examples.exits_c,
                  LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c, hp, hstep] at h
                exact h
              have hacc : mi_account_step segs ms model = .MachineOk (ms', model) := by
                rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
              refine exec_step_only segs ⟨ms, model⟩ _ [] ⟨ms', model⟩
                (sstep.instr ms model ms' model hh hp hacc)
                (sstep_instr_only segs ms model ms' hlazy hp hstep) ?_
              simpa only [List.nil_append] using ih ms' model hh hlazy hrec
          | MachineFault =>
              simp only [Examples.exits_c,
                LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c, hp, hstep] at h
              exact absurd h (by simp)
          | MachineUnmodeled =>
              simp only [Examples.exits_c,
                LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c, hp, hstep] at h
              exact absurd h (by simp)



theorem exit0_exits_c (sp : word) (rnd : EntryDraw) (argv envp : List (List byte))
    (uid hw : word) :
    Examples.exits_c Examples.exit0_segments verdict_accept 8
      (init_machine_state Examples.exit0_segments 0x100 demo_phdrs sp rnd argv envp uid hw)
    = true := by
  obtain ⟨mem, rom, hms⟩ :=
    Examples.PatchClassifyDemo.Verdicts.init_machine_state_abstracts Examples.exit0_segments
      0x100 demo_phdrs sp rnd argv envp uid hw
  rw [hms]
  let st0 : machine_state := Examples.PatchClassifyDemo.Verdicts.demo_init_state 0x100 sp mem rom
  let st1 : machine_state := { st0 with
      ms_regs := bvmapSet (17 : reg) (BitVec.ofInt 64 93) st0.ms_regs
      ms_pc_val := st0.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st2 : machine_state := { st1 with
      ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 0) st1.ms_regs
      ms_pc_val := st1.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st3 : machine_state := { st2 with ms_svc_pending := some (BitVec.ofInt 64 93) }
  have hpc0 : st0.ms_pc_val = BitVec.ofInt 64 0x100 := rfl
  have hf0 : fetch_word Examples.exit0_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0x05d00893) := rfl
  have h1 : step Examples.exit0_segments st0 = .MachineOk st1 :=
    Examples.PatchClassifyDemo.Verdicts.step_addi_a7 Examples.exit0_segments st0 _ hpc0 hf0
  have hpc1 : st1.ms_pc_val = BitVec.ofInt 64 0x100 + BitVec.ofInt 64 4 := rfl
  have hf1 : fetch_word Examples.exit0_segments (BitVec.ofInt 64 0x100 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00000513) := rfl
  have h2 : step Examples.exit0_segments st1 = .MachineOk st2 :=
    Examples.PatchClassifyDemo.Verdicts.step_addi_a0_0 Examples.exit0_segments st1 _ hpc1 hf1
  have hpc2 : st2.ms_pc_val
      = BitVec.ofInt 64 0x100 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4 := rfl
  have hf2 : fetch_word Examples.exit0_segments
      (BitVec.ofInt 64 0x100 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00000073) := rfl
  have ha7 : ms_reg st2 17 = BitVec.ofInt 64 93 := rfl
  have h3 : step Examples.exit0_segments st2 = .MachineOk st3 :=
    Examples.PatchClassifyDemo.Verdicts.step_ecall Examples.exit0_segments st2 _ hpc2 hf2 ha7
  have hp0 : st0.ms_svc_pending = none := rfl
  have hp1 : st1.ms_svc_pending = none := rfl
  have hp2 : st2.ms_svc_pending = none := rfl
  have hp3 : st3.ms_svc_pending = some (BitVec.ofInt 64 93) := rfl
  have hg : ms_gpr st3 0 = BitVec.ofInt 64 0 := rfl
  have hcode : ms_gpr st3 0 &&& BitVec.ofInt 64 255 = verdict_accept := by
    rw [hg]; decide
  have e0 : Examples.exits_c Examples.exit0_segments verdict_accept 8 st0
      = Examples.exits_c Examples.exit0_segments verdict_accept 7 st1 :=
    Examples.PatchClassifyDemo.Verdicts.exits_c_succ_none _ _ 7 st0 st1 hp0 h1
  have e1 : Examples.exits_c Examples.exit0_segments verdict_accept 7 st1
      = Examples.exits_c Examples.exit0_segments verdict_accept 6 st2 :=
    Examples.PatchClassifyDemo.Verdicts.exits_c_succ_none _ _ 6 st1 st2 hp1 h2
  have e2 : Examples.exits_c Examples.exit0_segments verdict_accept 6 st2
      = Examples.exits_c Examples.exit0_segments verdict_accept 5 st3 :=
    Examples.PatchClassifyDemo.Verdicts.exits_c_succ_none _ _ 5 st2 st3 hp2 h3
  have e3 : Examples.exits_c Examples.exit0_segments verdict_accept 5 st3 = true :=
    Examples.PatchClassifyDemo.Verdicts.exits_c_succ_exit _ _ 4 st3 _ hp3 (Or.inl rfl) hcode
  rw [e0, e1, e2, e3]

theorem exit0_exec (sp brk0 mbase : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) :
    exec Examples.exit0_segments
      (init_config Examples.exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp)
      (fun tr o => tr = [event.ExitEv verdict_accept (in_fs inp)]
                    ∧ exits_with verdict_accept tr o) := by
  unfold init_config
  refine exits_c_exec Examples.exit0_segments verdict_accept 8
    (init_machine_state Examples.exit0_segments 0x100 demo_phdrs sp rnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
    (init_model (segments_reserved Examples.exit0_segments) brk0 mbase sp lim inp)
    (m_halted_init_model _ _ _ _ _ _) rfl ?_
  exact exit0_exits_c sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap

theorem exit0_obs (sp brk0 mbase : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (tr : List event) :
    obs_trace Examples.exit0_segments
      (init_config Examples.exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) tr
    ↔ is_prefix tr [event.ExitEv verdict_accept (in_fs inp)] := by
  apply exec_obs_iff
  exact exec_conseq Examples.exit0_segments _ _ _ (exit0_exec sp brk0 mbase rnd lim inp)
    (fun tr' o h => ⟨h.1, exits_with_never_errors _ _ _ h.2⟩)

theorem exit0_never_errors (sp brk0 mbase : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) :
    coexec Examples.exit0_segments
      (init_config Examples.exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp)
      never_errors := by
  apply exec_coexec
  exact exec_conseq Examples.exit0_segments _ _ _ (exit0_exec sp brk0 mbase rnd lim inp)
    (fun tr o h => exits_with_never_errors _ _ _ h.2)

theorem exit0_omni_strong_equiv_any (en_source en_target : ExecEntry) (inp : ProcInput) :
    omni_strong_equiv Examples.exit0_image Examples.exit0_image en_source en_target inp := by
  obtain ⟨sps, brks, mbs, rnds⟩ := en_source
  obtain ⟨spt, brkt, mbt, rndt⟩ := en_target
  unfold omni_strong_equiv omni_equiv omni_trace_equiv
  simp only [omni_corun, omni_cosafe, Examples.exit0_image,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq Examples.exit0_segments _ _ _
      (exit0_never_errors sps brks mbs rnds source_alloc_limit inp)
      (fun tr o h => never_errors_covered _ tr o h)
  · intro P hP
    rw [cosafe_obs_iff _ _ P hP, cosafe_obs_iff _ _ P hP]
    constructor
    · intro Hall tr hobs
      exact Hall tr ((exit0_obs sps brks mbs rnds source_alloc_limit inp tr).mpr
        ((exit0_obs spt brkt mbt rndt target_alloc_limit inp tr).mp hobs))
    · intro Hall tr hobs
      exact Hall tr ((exit0_obs spt brkt mbt rndt target_alloc_limit inp tr).mpr
        ((exit0_obs sps brks mbs rnds source_alloc_limit inp tr).mp hobs))
  · exact exit0_never_errors spt brkt mbt rndt target_alloc_limit inp

theorem exit0_omni_strong_universal :
    omni_strong_universal_T Examples.exit0_image Examples.exit0_image := by
  intro en_s en_t inp _ _ _
  exact exit0_omni_strong_equiv_any en_s en_t inp

theorem exit0_strong_universal :
    strong_universal_T Examples.exit0_image Examples.exit0_image := by
  apply (strong_universal_iff _ _).mpr
  exact exit0_omni_strong_universal

def Exit0Image : MemImage := ⟨Examples.exit0_segments, 0x100, demo_phdrs⟩

theorem Exit0OmniChecked : OMNI_SPEC Exit0Image Exit0Image where
  omni_strong_universal := exit0_omni_strong_universal

theorem Exit0Checked : SPEC Exit0Image Exit0Image :=
  SpecOfOmni Exit0Image Exit0Image Exit0OmniChecked

/- -------------------------------------------------------------------------
   The abort stances, ascribed on the same pair
   ------------------------------------------------------------------------- -/

theorem exit0_strong_equiv_any (en_source en_target : ExecEntry) (inp : ProcInput) :
    strong_equiv Examples.exit0_image Examples.exit0_image en_source en_target inp := by
  exact (strong_equiv_iff _ _ _ _ inp).mpr
    (exit0_omni_strong_equiv_any en_source en_target inp)

theorem exit0_strong_universal_abort :
    strong_universal_T_abort Examples.exit0_image Examples.exit0_image := by
  intro en_s en_t inp _ _ _
  exact exit0_strong_equiv_any en_s en_t inp

theorem exit0_strong_universal_either :
    strong_universal_T_either Examples.exit0_image Examples.exit0_image := by
  intro en_s en_t inp _ _ _
  exact exit0_strong_equiv_any en_s en_t inp

theorem exit0_not_dies_by_signal (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ dies_by_signal (run Examples.exit0_image lim en inp) := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  rintro ⟨tr, sig, fs, Hobs, Hin⟩
  simp only [run, Examples.exit0_image,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage] at Hobs
  rw [exit0_obs] at Hobs
  cases tr with
  | nil => simp only [List.not_mem_nil] at Hin
  | cons e tr' =>
      obtain ⟨rfl, hp⟩ := Hobs
      cases tr' with
      | nil =>
          simp only [List.mem_singleton] at Hin
          cases Hin
      | cons e' tr'' => exact hp

theorem exit0_error_free_run (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    error_free (run Examples.exit0_image lim en inp) := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  rw [error_free_iff]
  simp only [omni_corun, Examples.exit0_image,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  exact exit0_never_errors sp brk0 mbase rnd lim inp

theorem exit0_strong_equiv_error_free_abort_any (en_source en_target : ExecEntry)
    (inp : ProcInput) :
    strong_equiv_error_free_abort Examples.exit0_image Examples.exit0_image
      en_source en_target inp := by
  obtain ⟨sps, brks, mbs, rnds⟩ := en_source
  obtain ⟨spt, brkt, mbt, rndt⟩ := en_target
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact exit0_error_free_run source_alloc_limit ⟨sps, brks, mbs, rnds⟩ inp
  · exact exit0_not_dies_by_signal source_alloc_limit ⟨sps, brks, mbs, rnds⟩ inp
  · exact exit0_error_free_run target_alloc_limit ⟨spt, brkt, mbt, rndt⟩ inp
  · exact exit0_not_dies_by_signal target_alloc_limit ⟨spt, brkt, mbt, rndt⟩ inp
  · intro tr
    simp only [run, Examples.exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
    rw [exit0_obs sps brks mbs rnds source_alloc_limit inp tr,
      exit0_obs spt brkt mbt rndt target_alloc_limit inp tr]

theorem exit0_strong_universal_error_free_abort :
    strong_universal_error_free_T_abort Examples.exit0_image Examples.exit0_image := by
  intro en_s en_t inp _ _ _
  exact exit0_strong_equiv_error_free_abort_any en_s en_t inp

theorem exit0_strong_universal_error_free :
    strong_universal_error_free_T Examples.exit0_image Examples.exit0_image := by
  intro en_s en_t inp _ _ _
  obtain ⟨Hsef, Htef, Htr⟩ := exit0_strong_equiv_error_free_abort_any en_s en_t inp
  exact ⟨error_free_unkilled_error_free _ Hsef, error_free_unkilled_error_free _ Htef, Htr⟩

theorem exit0_strong_universal_error_free_either :
    strong_universal_error_free_T_either Examples.exit0_image Examples.exit0_image :=
  ⟨exit0_strong_universal_error_free, exit0_strong_universal_error_free_abort⟩

theorem exit0_strong_universal_scfg_abort :
    strong_universal_T_scfg_abort may_fail_cfg Examples.exit0_image Examples.exit0_image := by
  exact (strong_universal_T_scfg_abort_may_fail _ _).mpr exit0_strong_universal_abort

theorem exit0_strong_universal_scfg_either :
    strong_universal_T_scfg_either may_fail_cfg Examples.exit0_image Examples.exit0_image := by
  exact (strong_universal_T_scfg_either_may_fail _ _).mpr exit0_strong_universal_either

theorem exit0_strong_universal_error_free_scfg_abort :
    strong_universal_error_free_T_scfg_abort may_fail_cfg Examples.exit0_image
      Examples.exit0_image := by
  exact (strong_universal_error_free_T_scfg_abort_may_fail _ _).mpr
    exit0_strong_universal_error_free_abort

theorem exit0_strong_universal_error_free_scfg :
    strong_universal_error_free_T_scfg may_fail_cfg Examples.exit0_image Examples.exit0_image := by
  exact (strong_universal_error_free_T_scfg_may_fail _ _).mpr
    exit0_strong_universal_error_free

theorem exit0_strong_universal_error_free_scfg_either :
    strong_universal_error_free_T_scfg_either may_fail_cfg Examples.exit0_image
      Examples.exit0_image :=
  ⟨exit0_strong_universal_error_free_scfg, exit0_strong_universal_error_free_scfg_abort⟩

def MayFailCfg : SPURIOUS_CFG := ⟨may_fail_cfg⟩

theorem Exit0ErrorFreeEitherChecked :
    SPEC_ERROR_FREE_EITHER Exit0Image Exit0Image where
  strong_universal_error_free := exit0_strong_universal_error_free_either

theorem Exit0ScfgAbortChecked : SPEC_SCFG_ABORT MayFailCfg Exit0Image Exit0Image where
  strong_universal := exit0_strong_universal_scfg_abort

theorem Exit0ScfgEitherChecked : SPEC_SCFG_EITHER MayFailCfg Exit0Image Exit0Image where
  strong_universal := exit0_strong_universal_scfg_either

theorem Exit0ErrorFreeScfgAbortChecked :
    SPEC_ERROR_FREE_SCFG_ABORT MayFailCfg Exit0Image Exit0Image where
  strong_universal_error_free := exit0_strong_universal_error_free_scfg_abort

theorem Exit0ErrorFreeScfgEitherChecked :
    SPEC_ERROR_FREE_SCFG_EITHER MayFailCfg Exit0Image Exit0Image where
  strong_universal_error_free := exit0_strong_universal_error_free_scfg_either

/- -------------------------------------------------------------------------
   The classifier-side reading, and the check that bites
   ------------------------------------------------------------------------- -/

theorem exit0_omni_exits_zero :
    omni_run Examples.exit0_image demo_limit demo_entry demo_proc_input
      (exits_with verdict_accept) := by
  exact (must_exit_with_iff _ _ _ _ _).mp Examples.exit0_image_must_exit_zero

theorem exit0_omni_exits_zero_direct :
    omni_run Examples.exit0_image demo_limit demo_entry demo_proc_input
      (exits_with verdict_accept) := by
  simp only [omni_run, Examples.exit0_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  exact exec_conseq _ _ _ _ (exit0_exec _ _ _ _ demo_limit demo_proc_input)
    (fun tr o h => h.2)

theorem exit0_omni_exits_zero_legacy :
    must_exit_with verdict_accept Examples.exit0_image demo_limit demo_entry
      demo_proc_input := by
  exact (must_exit_with_iff _ _ _ _ _).mpr exit0_omni_exits_zero_direct

theorem exit0_omni_not_exits_one :
    ¬ omni_run Examples.exit0_image demo_limit demo_entry demo_proc_input
        (exits_with verdict_reject) := by
  intro H
  simp only [omni_run, Examples.exit0_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage] at H
  obtain ⟨tr, o, Hm, Hx⟩ := exec_realizes _ _ _ H
  obtain ⟨-, Hx0⟩ := exec_sound _ _ _
    (exit0_exec (BitVec.ofInt 64 0x7fff80000000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 mmap_base_max) demo_draw demo_limit demo_proc_input) _ _ Hm
  cases o with
  | OHalt c =>
      obtain ⟨h1, -⟩ := Hx
      obtain ⟨h2, -⟩ := Hx0
      rw [h1] at h2
      exact absurd (Option.some.inj h2) (by decide)
  | OError c => exact Hx
end Part2

/- =========================================================================
   PART 3 — the undecodable image refutes them

   Every error-related omni postcondition fails on it: its first fetch
   leaves the modeled surface, at the demo entry and at either role budget,
   and `bh_unmodeled` blocks `covered` and (through
   `run_unmodeled_errors`) `never_errors` while it ENTITLES `errors` and
   `uncovered`.  The trace conjunct is what separates it from the exit-0
   image, and the two validity lemmas (`demo_entry_valid_exit0`,
   `demo_entry_valid_undecodable`) are what make each refutation land at a
   VALID triple rather than at an entry `agree` would not quantify over.
   ========================================================================= -/

section Part3

open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.MustExit

theorem undecodable_unmodeled_at_demo_entry (lim : Int) :
    (run Examples.undecodable_image lim demo_entry demo_proc_input).bh_unmodeled := by
  simp only [run, Examples.undecodable_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  unfold init_config
  refine reaches_unmodeled_intro _ _ _ rfl rfl ?_
  have hst : init_machine_state Examples.undecodable_segments 0x100 demo_phdrs
      (BitVec.ofInt 64 0x7fff80000000) demo_draw
      demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
      demo_proc_input.in_hwcap
      = init_machine_state Examples.undecodable_segments 0x100 demo_phdrs
        (BitVec.ofInt 64 0x7fff80000000) demo_draw [[]] [] demo_uid demo_hwcap := rfl
  rw [hst]
  rfl

theorem undecodable_omni_not_covered (lim : Int) :
    ¬ omni_corun Examples.undecodable_image lim demo_entry demo_proc_input
        (covered Examples.undecodable_segments) := by
  intro H
  exact (bh_unmodeled_iff Examples.undecodable_image lim demo_entry demo_proc_input).mpr H
    (undecodable_unmodeled_at_demo_entry lim)

theorem undecodable_omni_not_never_errors (lim : Int) :
    ¬ omni_corun Examples.undecodable_image lim demo_entry demo_proc_input never_errors := by
  intro H
  exact (bh_errors_iff Examples.undecodable_image lim demo_entry demo_proc_input).mpr H
    (run_unmodeled_errors _ _ _ _ (undecodable_unmodeled_at_demo_entry lim))

theorem undecodable_omni_may_uncovered (lim : Int) :
    omni_may Examples.undecodable_image lim demo_entry demo_proc_input
      (uncovered Examples.undecodable_segments) := by
  exact (bh_unmodeled_may_iff Examples.undecodable_image lim demo_entry demo_proc_input).mp
    (undecodable_unmodeled_at_demo_entry lim)

theorem undecodable_omni_no_exit (lim : Int) (code : word) :
    ¬ omni_run Examples.undecodable_image lim demo_entry demo_proc_input (exits_with code) := by
  intro H
  exact must_exit_with_refuted_by_error code _ lim _ _
    (run_unmodeled_errors _ _ _ _ (undecodable_unmodeled_at_demo_entry lim))
    ((must_exit_with_iff code _ lim _ _).mpr H)

theorem undecodable_omni_errors (lim : Int) :
    omni_run Examples.undecodable_image lim demo_entry demo_proc_input errors := by
  simp only [omni_run, Examples.undecodable_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  unfold init_config
  have hst : init_machine_state Examples.undecodable_segments 0x100 demo_phdrs
      (BitVec.ofInt 64 0x7fff80000000) demo_draw
      demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
      demo_proc_input.in_hwcap
      = init_machine_state Examples.undecodable_segments 0x100 demo_phdrs
        (BitVec.ofInt 64 0x7fff80000000) demo_draw [[]] [] demo_uid demo_hwcap := rfl
  have hacc : mi_account_step Examples.undecodable_segments
      (init_machine_state Examples.undecodable_segments 0x100 demo_phdrs
        (BitVec.ofInt 64 0x7fff80000000) demo_draw [[]] [] demo_uid demo_hwcap)
      (init_model (segments_reserved Examples.undecodable_segments)
        (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max)
        (BitVec.ofInt 64 0x7fff80000000) lim demo_proc_input) = .MachineUnmodeled := by
    rw [← hst]
    rfl
  refine exec.step ⟨_, _⟩ errors rfl ⟨[], .SError, ?_⟩ (fun _ _ => True.intro) ?_
  · exact sstep.instr_unmodeled _ _ rfl rfl hacc
  · intro evs c' hss
    exact absurd hss
      (Examples.unmodeled_no_next _ _ _ evs c' rfl hacc)

theorem undecodable_source_refutes_omni_strong_universal :
    ¬ omni_strong_universal_T Examples.undecodable_image Examples.exit0_image := by
  intro H
  obtain ⟨Hcov, -⟩ := H demo_entry demo_entry demo_proc_input
    (Examples.demo_entry_valid_undecodable _ demo_input_valid)
    (Examples.demo_entry_valid_exit0 _ demo_input_valid)
    demo_input_valid
  exact undecodable_omni_not_covered source_alloc_limit Hcov

theorem undecodable_cosafe_nil (lim : Int) :
    omni_cosafe Examples.undecodable_image lim demo_entry demo_proc_input
      (fun tr => tr = []) := by
  simp only [omni_cosafe, Examples.undecodable_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  unfold init_config
  have hst : init_machine_state Examples.undecodable_segments 0x100 demo_phdrs
      (BitVec.ofInt 64 0x7fff80000000) demo_draw
      demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
      demo_proc_input.in_hwcap
      = init_machine_state Examples.undecodable_segments 0x100 demo_phdrs
        (BitVec.ofInt 64 0x7fff80000000) demo_draw [[]] [] demo_uid demo_hwcap := rfl
  have hacc : mi_account_step Examples.undecodable_segments
      (init_machine_state Examples.undecodable_segments 0x100 demo_phdrs
        (BitVec.ofInt 64 0x7fff80000000) demo_draw [[]] [] demo_uid demo_hwcap)
      (init_model (segments_reserved Examples.undecodable_segments)
        (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max)
        (BitVec.ofInt 64 0x7fff80000000) lim demo_proc_input) = .MachineUnmodeled := by
    rw [← hst]
    rfl
  refine cosafe_intro _ _ _ rfl ?_
  intro evs c' hss
  exact absurd hss (Examples.unmodeled_no_next _ _ _ evs c' rfl hacc)

theorem exit0_vs_undecodable_refutes_omni_strong_universal :
    ¬ omni_strong_universal_T Examples.exit0_image Examples.undecodable_image := by
  intro H
  obtain ⟨-, Hall | ⟨Htr, -⟩⟩ := H demo_entry demo_entry demo_proc_input
    (Examples.demo_entry_valid_exit0 _ demo_input_valid)
    (Examples.demo_entry_valid_undecodable _ demo_input_valid)
    demo_input_valid
  · simp only [omni_run, Examples.exit0_image, demo_entry,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage] at Hall
    obtain ⟨tr, o, Hm, Hx⟩ := exec_realizes _ _ _ Hall
    exact (exits_with_never_errors verdict_accept tr o
      (exec_sound _ _ _
        (exit0_exec (BitVec.ofInt 64 0x7fff80000000) (BitVec.ofInt 64 0x1000)
          (BitVec.ofInt 64 mmap_base_max) demo_draw source_alloc_limit demo_proc_input)
        _ _ Hm).2) Hx
  · have hone := (Htr (fun tr => tr = []) prefix_closed_nil).mpr
      (undecodable_cosafe_nil target_alloc_limit)
    simp only [omni_cosafe, Examples.exit0_image, demo_entry,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage] at hone
    obtain ⟨tr, o, Hm, hq⟩ := exec_realizes _ _ _
      (exit0_exec (BitVec.ofInt 64 0x7fff80000000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 mmap_base_max) demo_draw source_alloc_limit demo_proc_input)
    cases o with
    | OHalt c' =>
        obtain ⟨hstar, -⟩ := mexec_halt_star _ _ _ _ Hm c' rfl
        have hnil : tr = [] :=
          cosafe_star Examples.exit0_segments _ (fun tr => tr = []) tr c' hone hstar
        rw [hnil] at hq
        cases hq.1
    | OError c' =>
        exact (exec_sound _ _ _
          (exit0_exec (BitVec.ofInt 64 0x7fff80000000) (BitVec.ofInt 64 0x1000)
            (BitVec.ofInt 64 mmap_base_max) demo_draw source_alloc_limit demo_proc_input)
          _ _ Hm).2

end Part3


/- =========================================================================
   PART 4 — the `ebreak` fixtures

   The fixtures and their instruction-level lemmas first: they are named by
   `Checks.BudgetPremise` (PART 2's "a fault the interpreter raises for its
   own reasons") and are stated over `demo_proc_input` alone.  The omni
   statements then follow, stated over the `Checks.Examples` entry and run
   fixtures — `ebreak_omni_errors` is the escape firing, `ebreak_omni_covered`
   says the crash is nonetheless inside the model's surface, and
   `ebreak_omni_not_never_errors` says the two postconditions are therefore
   distinct on a real image.
   ========================================================================= -/

/-- One `ebreak` at 0x100 (0x00100073, little-endian): a fault the
    model MODELS — a real process dies there too — as opposed to the
    undecodable word, where the model gives up. -/
def ebreak_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["73001000"]

def ebreak_segments : List Segment := [ebreak_segment]

def ebreak_image : Image :=
  LinuxSem.EquivalenceDefinition.Equivalence.mkImage ebreak_segments 0x100
    demo_phdrs

def ebreak_ms : machine_state :=
  init_machine_state ebreak_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
    demo_draw
    demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
    demo_proc_input.in_hwcap

def ebreak_model (lim : Int) : Model :=
  init_model (segments_reserved ebreak_segments) (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000) lim demo_proc_input

theorem ebreak_config (lim : Int) :
    init_config ebreak_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim
      demo_proc_input
    = ⟨ebreak_ms, ebreak_model lim⟩ := rfl

theorem ebreak_faults : RiscvSemantics.step ebreak_segments ebreak_ms = .MachineFault := rfl

theorem ebreak_only (lim : Int) (evs : List event) (st : step_to)
    (hss : sstep ebreak_segments ⟨ebreak_ms, ebreak_model lim⟩ evs st) :
    evs = [] ∧ st = .SError :=
  sstep_fault_only ebreak_segments ebreak_ms (ebreak_model lim) rfl rfl ebreak_faults evs st hss

/-! ### PARTS 2 and 3 — the omni walk's shape

    Every declaration of the two parts is stated over
    `Checks.Examples.exit0_segments`, `.exit0_image`, `.undecodable_image`,
    `.demo_entry`, `.exits_c`, `.demo_input_valid`,
    `.demo_entry_valid_exit0` and `.demo_entry_valid_undecodable`, and one
    lemma carries them: `exits_c_exec`, at the head of PART 2 above — the
    same reflection over `exits_c` as
    `Checks.Examples.exits_c_must_exit_at`, with the TRACE and the exit
    code recorded together, which is what a trace statement needs and what
    `must_exit_at` cannot give.

    `sstep_exit_only` is its one helper: the inversion
    `Verdicts.must_exit_at_exit_pending` performs, with the transition's
    shape recorded instead of a `must_exit_at` conclusion.

    `exit0_exec`, `exit0_obs`, `exit0_never_errors` and every statement
    built on them are one-line consequences of `exits_c_exec`, and PART 3's
    refutations are one-line consequences of `Checks.Examples`'
    `undecodable_step_unmodeled_at_demo_entry` and `unmodeled_no_next`.
    Neither part needs a second reflective walk. -/


/- =========================================================================
   PART 4 (the omni statements) — a modeled CRASH separates the three
   error postconditions
   ========================================================================= -/

/-- Every execution errors: the escape fires, so `omni_run … errors`
    holds of an image whose one instruction faults. -/
theorem ebreak_omni_errors (lim : Int) :
    omni_run ebreak_image lim demo_entry demo_proc_input errors := by
  simp only [omni_run, ebreak_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  rw [ebreak_config]
  have hfault : sstep ebreak_segments ⟨ebreak_ms, ebreak_model lim⟩ [] .SError :=
    sstep.instr_fault _ _ rfl rfl (by no_lazy; rw [ebreak_faults])
  refine exec.step ⟨ebreak_ms, ebreak_model lim⟩ errors (by rfl) ⟨[], .SError, hfault⟩
    (fun evs hss => True.intro) ?_
  intro evs c' hss
  exact absurd (ebreak_only lim evs (.SNext c') hss).2 (by simp)

/-- ... the crash is COVERED, because the configuration it is taken from
    is one the model has an answer for ... -/
theorem ebreak_omni_covered (lim : Int) :
    omni_corun ebreak_image lim demo_entry demo_proc_input (covered ebreak_segments) := by
  simp only [omni_corun, ebreak_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  rw [ebreak_config]
  refine coexec_step _ _ _ (by rfl) ?_ ?_
  · intro evs hss
    rintro ⟨-, (⟨-, Hun⟩ | ⟨x8, Hsvc, -⟩)⟩
    · no_lazy_in Hun
      dsimp only at Hun
      rw [ebreak_faults] at Hun
      exact absurd Hun (by simp)
    · rw [show ebreak_ms.ms_svc_pending = none from rfl] at Hsvc
      exact absurd Hsvc (by simp)
  · intro evs c' hss
    exact absurd (ebreak_only lim evs (.SNext c') hss).2 (by simp)

/-- ... and it is NOT error-free: the three postconditions are distinct
    on a real image. -/
theorem ebreak_omni_not_never_errors (lim : Int) :
    ¬ omni_corun ebreak_image lim demo_entry demo_proc_input never_errors := by
  intro H
  simp only [omni_corun, ebreak_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage] at H
  rw [ebreak_config] at H
  have hmem := mexec.error (⟨ebreak_ms, ebreak_model lim⟩ : config) []
    (sstep.instr_fault _ _ rfl rfl (by no_lazy; rw [ebreak_faults]))
  have hne := coexec_sound ebreak_segments ⟨ebreak_ms, ebreak_model lim⟩ []
    (.OError ⟨ebreak_ms, ebreak_model lim⟩) hmem never_errors H
  simp only [never_errors, is_error] at hne
  exact hne trivial

theorem ebreak_omni_may_errors (lim : Int) :
    omni_may ebreak_image lim demo_entry demo_proc_input errors := by
  rw [← bh_errors_may_iff]
  exact run_all_errors_errors _ _ _ _ (by rw [bh_all_errors_iff]; exact ebreak_omni_errors lim)

/-- The escape, positively: a crashing source frees ANY target, even the
    undecodable one, at this triple. -/
theorem ebreak_source_omni_strong_equiv_any (T : Image) (et : ExecEntry) :
    omni_strong_equiv ebreak_image T demo_entry et demo_proc_input := by
  refine ⟨?_, Or.inl ?_⟩
  · exact ebreak_omni_covered source_alloc_limit
  · exact ebreak_omni_errors source_alloc_limit

theorem ebreak_frees_undecodable_target :
    omni_strong_equiv ebreak_image undecodable_image demo_entry demo_entry demo_proc_input :=
  ebreak_source_omni_strong_equiv_any undecodable_image demo_entry

/-- ... and the same crash REFUTES the error-free shape, which has no
    escape. -/
theorem ebreak_refutes_omni_error_free :
    ¬ omni_strong_equiv_error_free ebreak_image ebreak_image demo_entry demo_entry
        demo_proc_input :=
  omni_strong_equiv_error_free_no_all_errors_escape _ _ _ _ _
    (ebreak_omni_errors source_alloc_limit)

/- =========================================================================
   PART 5 — `exec`/`coexec` agreement is strictly weaker than trace equality
   ========================================================================= -/

/-- One `jal x0, 0` at 0x100 (0x0000006f, little-endian): the process
    spins forever and emits nothing. -/
def loop_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["6f000000"]

def loop_segments : List Segment := [loop_segment]

def loop_image : Image :=
  LinuxSem.EquivalenceDefinition.Equivalence.mkImage loop_segments 0x100
    demo_phdrs

/-- `write(1, 0x100, 1)` — `addi a7, x0, 64; addi a0, x0, 1; addi a1, x0,
    0x100; addi a2, x0, 1; ecall` — then the same `jal x0, 0`: one byte of
    its own code (0x93) reaches stdout, then the process spins forever. -/
def wloop_segment : Segment where
  seg_base := 0x100
  seg_size := 24
  seg_perms := "r-x"
  seg_bytes := ["93080004130510009305001013061000730000006f000000"]

def wloop_segments : List Segment := [wloop_segment]

def wloop_image : Image :=
  LinuxSem.EquivalenceDefinition.Equivalence.mkImage wloop_segments 0x100
    demo_phdrs

/-- The byte the write delivers: the low byte of `addi a7, x0, 64`. -/
def wloop_byte : byte := BitVec.ofInt 8 0x93

def wloop_trace : List event := [event.WriteEv (BitVec.ofInt 64 1) wloop_byte]

def loop_ms : machine_state :=
  init_machine_state loop_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
    demo_draw
    demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
    demo_proc_input.in_hwcap

def loop_model (lim : Int) : Model :=
  init_model (segments_reserved loop_segments) (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000) lim demo_proc_input

def loop_c (lim : Int) : config := ⟨loop_ms, loop_model lim⟩

theorem loop_config (lim : Int) :
    init_config loop_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim
      demo_proc_input = loop_c lim := rfl

/-! The one instruction every step lemma below reduces: unfold the
    interpreter, fix the pc (the only field `with_mem` disturbs), reduce.
    `RiscvSemantics.step` reads the frontier's own hex image, so the
    memory abstraction costs nothing. -/
theorem with_mem_ms_pc (ms : machine_state) (mem : word → Option byte) :
    ms_pc (with_mem ms mem) = ms.ms_pc_val := rfl

macro "istep" : tactic =>
  `(tactic| (simp only [RiscvSemantics.step, step_accesses, with_mem_ms_pc]; rfl))

/-- `jal x0, 0` maps the initial state to itself: the pc gains 0 and the
    write to x0 is dropped, so nothing changes. -/
theorem loop_fix (mem : word → Option byte) :
    RiscvSemantics.step loop_segments (with_mem loop_ms mem)
      = .MachineOk (with_mem loop_ms mem) := by
  istep

theorem loop_only (lim : Int) (evs : List event) (st : step_to)
    (hss : sstep loop_segments (loop_c lim) evs st) :
    evs = [] ∧ st = .SNext (loop_c lim) := by
  rw [show loop_c lim = ⟨with_mem loop_ms loop_ms.ms_mem, loop_model lim⟩ from
        (congrArg (fun s => (⟨s, loop_model lim⟩ : config)) (with_mem_eta loop_ms)).symm]
  exact sstep_instr_only loop_segments (with_mem loop_ms loop_ms.ms_mem) (loop_model lim)
    (with_mem loop_ms loop_ms.ms_mem) rfl rfl (loop_fix loop_ms.ms_mem) evs st hss

theorem loop_coexec_any (lim : Int) (Q : post) :
    coexec loop_segments (loop_c lim) Q :=
  fix_coexec_any loop_segments (loop_c lim) rfl (loop_only lim) Q

theorem loop_no_exec (lim : Int) (Q : post) : ¬ exec loop_segments (loop_c lim) Q :=
  fix_no_exec loop_segments (loop_c lim) rfl (loop_only lim) Q

theorem loop_obs_nil (lim : Int) (tr : List event) :
    obs_trace loop_segments (loop_c lim) tr → tr = [] :=
  fix_obs_nil loop_segments (loop_c lim) (loop_only lim) tr

/-! The write-then-loop run, one transition at a time.  `run_steps`
    walks the instruction stream; the states along it are named by
    their step count, and every step lemma is stated with the memory
    abstracted. -/
def run_steps : Nat → List Segment → machine_state → Option machine_state
  | 0, _, ms => some ms
  | n + 1, segs, ms =>
    match RiscvSemantics.step segs ms with
    | .MachineOk ms' => run_steps n segs ms'
    | .MachineFault => none
    | .MachineUnmodeled => none

def wloop_ms0 : machine_state :=
  init_machine_state wloop_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
    demo_draw
    demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
    demo_proc_input.in_hwcap

def wloop_msk (k : Nat) : machine_state :=
  match run_steps k wloop_segments wloop_ms0 with
  | some ms => ms
  | none => wloop_ms0

/-- The state after `k` instructions, with the memory of the real initial
    state — which no instruction of this image changes. -/
def wloop_s (k : Nat) : machine_state := with_mem (wloop_msk k) wloop_ms0.ms_mem

def wloop_model (lim : Int) : Model :=
  init_model (segments_reserved wloop_segments) (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000) lim demo_proc_input

def wloop_c (lim : Int) : config := ⟨wloop_s 0, wloop_model lim⟩

theorem wloop_config (lim : Int) :
    init_config wloop_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim
      demo_proc_input = wloop_c lim := by
  simp only [wloop_c, wloop_s, wloop_msk, run_steps]
  rw [← with_mem_eta wloop_ms0]
  rfl

/-- The effect the write is forced to have: one byte copied in from
    0x100, one byte reported written. -/
def wloop_eff : SyscallEffect :=
  with_copyins [(BitVec.ofInt 64 0x100, 1)] (mkEffect (BitVec.ofInt 64 1) [] [])

/-- After the syscall: the return value is in a0 and the pc sits on
    the `jal`. -/
def wloop_s6 : machine_state := advance_past_svc (apply_effect (wloop_s 5) wloop_eff)

theorem wloop_step : ∀ k, k < 5 → ∀ mem,
    RiscvSemantics.step wloop_segments (with_mem (wloop_msk k) mem)
      = .MachineOk (with_mem (wloop_msk (k + 1)) mem) := by
  intro k Hk mem
  rcases k with _ | _ | _ | _ | _ | k
  · istep
  · istep
  · istep
  · istep
  · istep
  · omega

theorem wloop_svc5 : (wloop_s 5).ms_svc_pending = some (BitVec.ofInt 64 64) := by
  decide

theorem wloop_fix (mem : word → Option byte) :
    RiscvSemantics.step wloop_segments (with_mem wloop_s6 mem)
      = .MachineOk (with_mem wloop_s6 mem) := by
  istep

/-- The pending-syscall field along the five instruction steps: the ecall
    is only reached at step five. -/
theorem wloop_svc_none (k : Nat) (Hk : k < 5) : (wloop_s k).ms_svc_pending = none := by
  rcases k with _ | _ | _ | _ | _ | k <;> first | decide | omega

/-- The five instruction transitions, each the only one from its
    configuration. -/
theorem wloop_instr_only (lim : Int) : ∀ k, k < 5 → ∀ evs st,
    sstep wloop_segments ⟨wloop_s k, wloop_model lim⟩ evs st →
    evs = [] ∧ st = .SNext ⟨wloop_s (k + 1), wloop_model lim⟩ := by
  intro k Hk evs st hss
  exact sstep_instr_only _ _ _ _ rfl (wloop_svc_none k Hk)
    (wloop_step k Hk wloop_ms0.ms_mem) evs st hss

theorem wloop_instr_sstep (lim : Int) : ∀ k, k < 5 →
    sstep wloop_segments ⟨wloop_s k, wloop_model lim⟩ []
      (.SNext ⟨wloop_s (k + 1), wloop_model lim⟩) := by
  intro k Hk
  have hstep : mi_account_step wloop_segments (wloop_s k) (wloop_model lim)
      = .MachineOk (wloop_s (k + 1), wloop_model lim) := by
    no_lazy
    simp only [wloop_s]
    rw [wloop_step k Hk wloop_ms0.ms_mem]
  exact sstep.instr _ _ _ _ rfl (wloop_svc_none k Hk) hstep

/-- At the ecall.  The dispatcher at number 64 IS the write spec ... -/
theorem write_dispatch_iff (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (E : (i.in_sysno.toNat : Int) = 64) :
    Specs.syscall_spec i m o ↔
      LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite.write_spec
        (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := by
  rw [Specs.syscall_spec, Sys.Dispatch.dispatch, E]
  rfl

/-- The syscall input at the ecall of the write-then-loop image, named once
    so the staged evaluator below does not repeat it. -/
abbrev wloop_i : SyscallInput := sys_input wloop_segments (wloop_s 5) (BitVec.ofInt 64 64)

/-- The five facts the walk of `check_write`'s CHANNEL arm reads off this
    input.  Every one is a `decide` (a `rfl` where no `DecidableEq`
    exists), and together they are what makes the arm's `if`-chain a
    closed computation: the descriptor is stdout, the count gate passes,
    the request moves one byte, and that byte is the image's own first
    opcode. -/
theorem wloop_fd (lim : Int) :
    fd_lookup (m_fds (wloop_model lim)) (fd32 (in_arg wloop_i 0))
      = some (FdEntry.FdChannel (BitVec.ofInt 64 1)) := rfl

theorem wloop_chan : w_is0 (1#64) = false := by decide

theorem wloop_range : modeled_rw_range (in_arg wloop_i 1) (in_arg wloop_i 2) = true := by
  decide

theorem wloop_count : w_is0 (in_arg wloop_i 2) = false := by decide

theorem wloop_source : write_source wloop_i.in_mem (in_arg wloop_i 1) (in_arg wloop_i 2)
    = [BitVec.ofInt 8 0x93] := by decide

/-- THE STAGED EVALUATOR, one arm: `check_write`'s channel branch at this
    input, reduced past every argument gate.  What is left is the
    claimed-effect test alone, so an accepted verdict forces the effect.
    This is a per-arm staged evaluator, applied to the
    one arm this file needs. -/
theorem check_write_wloop_walk (lim : Int) (eff : SyscallEffect) :
    check_write wloop_i (fd32 (in_arg wloop_i 0)) (in_arg wloop_i 1) (in_arg wloop_i 2)
      eff (wloop_model lim)
    = (match eff with
       | ⟨ret, [], [], [], [], copyins⟩ =>
           if decide (1 ≤ (ret.toNat : Int)) && decide ((ret.toNat : Int) ≤ 1) then
             if LinuxSem.Checks.Sys.Prelude.access_ranges_eqb copyins
                  [(in_arg wloop_i 1, ret.toNat)] then
               .CheckOk (wloop_model lim)
                 (List.map (event.WriteEv (BitVec.ofInt 64 1)) (List.take ret.toNat
                   [BitVec.ofInt 8 0x93]))
             else .CheckReject
           else .CheckReject
       | _ => .CheckReject) := by
  simp [check_write, wloop_fd, wloop_chan, wloop_range, wloop_count, wloop_source]
  rfl

/-- The inversion the walk above yields: an ACCEPTED outcome at this
    input is the one `wloop_eff`/`wloop_trace` name.  Read off the two
    surviving tests — the claimed return is one byte, and the ledger is
    exactly the range that byte came from. -/
theorem check_write_wloop_inv (lim : Int) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (h : check_write wloop_i (fd32 (in_arg wloop_i 0)) (in_arg wloop_i 1)
           (in_arg wloop_i 2) eff (wloop_model lim) = .CheckOk m' evs) :
    eff = wloop_eff ∧ m' = wloop_model lim ∧ evs = wloop_trace := by
  rw [check_write_wloop_walk] at h
  cases eff with
  | mkEffectU ret ws zs us cs ci =>
    cases ws <;> cases zs <;> cases us <;> cases cs
    · dsimp only at h
      by_cases h1 : (decide (1 ≤ (ret.toNat : Int)) &&
          decide ((ret.toNat : Int) ≤ 1)) = true
      · rw [ite_eq_left h1] at h
        by_cases h2 : LinuxSem.Checks.Sys.Prelude.access_ranges_eqb ci
            [(in_arg wloop_i 1, ret.toNat)] = true
        · rw [ite_eq_left h2] at h
          simp only [LinuxSem.Checks.Sys.Prelude.check_result.CheckOk.injEq]
            at h
          obtain ⟨hm, hev⟩ := h
          have hret : ret = BitVec.ofInt 64 1 := by
            apply BitVec.eq_of_toNat_eq
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
            have hle : ret.toNat ≤ 1 := by exact_mod_cast h1.2
            have hge : 1 ≤ ret.toNat := by exact_mod_cast h1.1
            rw [BitVec.toNat_ofInt]
            omega
          subst hret
          have hci : ci = [(in_arg wloop_i 1, 1)] := by
            cases ci with
            | nil => simp [LinuxSem.Checks.Sys.Prelude.access_ranges_eqb] at h2
            | cons p tl =>
              obtain ⟨a, n⟩ := p
              cases tl with
              | nil =>
                simp only [LinuxSem.Checks.Sys.Prelude.access_ranges_eqb,
                  Bool.and_eq_true, beq_iff_eq, bv_eqb] at h2
                obtain ⟨⟨hab, hnk⟩, -⟩ := h2
                obtain rfl : a = in_arg wloop_i 1 := hab
                obtain rfl : n = 1 := hnk
                rfl
              | cons q tl' =>
                simp [LinuxSem.Checks.Sys.Prelude.access_ranges_eqb] at h2
          rw [hci]
          refine ⟨rfl, hm.symm, ?_⟩
          simpa [wloop_trace, wloop_byte] using hev.symm
        · rw [ite_eq_right h2] at h
          exact absurd h (by simp)
      · rw [ite_eq_right h1] at h
        exact absurd h (by simp)
    all_goals (dsimp only at h; exact absurd h (by simp))

/-- The per-arm result, in the form the spec side needs: `syscall_spec`
    at this input admits the one effect, model and event list. -/
theorem wloop_write_forced (lim : Int) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (Hspec : Specs.syscall_spec wloop_i (wloop_model lim) (.ok eff m' evs)) :
    eff = wloop_eff ∧ m' = wloop_model lim ∧ evs = wloop_trace := by
  refine check_write_wloop_inv lim eff m' evs ?_
  rw [← check_syscall_write wloop_i eff (wloop_model lim) (by decide)]
  exact check_syscall_complete_ok wloop_i eff (wloop_model lim) m' evs Hspec

theorem wloop_checker (lim : Int) :
    check_syscall wloop_i wloop_eff (wloop_model lim) = .CheckOk (wloop_model lim) wloop_trace := by
  rw [check_syscall_write wloop_i wloop_eff (wloop_model lim) (by decide),
    check_write_wloop_walk]
  simp [wloop_eff]
  rfl

/-- The syscall transition itself. -/
theorem wloop_syscall_sstep (lim : Int) :
    sstep wloop_segments ⟨wloop_s 5, wloop_model lim⟩ wloop_trace
      (.SNext ⟨wloop_s6, wloop_model lim⟩) := by
  have hspec : Specs.syscall_spec wloop_i (wloop_model lim)
      (.ok wloop_eff (wloop_model lim) wloop_trace) :=
    (check_syscall_ok_iff wloop_i wloop_eff (wloop_model lim) (wloop_model lim)
      wloop_trace).mp (wloop_checker lim)
  have hmat : materialize_model_accesses (wloop_model lim)
      (syscall_effect_accesses wloop_eff) = some (wloop_model lim) :=
    materialize_model_accesses_no_lazy _ _ rfl
  change sstep wloop_segments ⟨wloop_s 5, wloop_model lim⟩ wloop_trace
    (.SNext ⟨advance_past_svc (apply_effect (wloop_s 5) wloop_eff), wloop_model lim⟩)
  exact sstep.syscall (ms := wloop_s 5) (model := wloop_model lim)
    (x8 := BitVec.ofInt 64 64) (eff := wloop_eff) (model' := wloop_model lim)
    (model'' := wloop_model lim) (evs := wloop_trace) rfl wloop_svc5 hspec rfl hmat

/-- The one ecall transition, and the only one.  `Checks` has no
    `sstep` inversion of its own, but `Common/Nodes.lean` does
    (`sstep_svc_inv`, the same inversion `Common`'s write nodes use), and
    it is phrased through the CHECKER — which is exactly what the staged
    evaluator above pins.  So the walk is: invert to the checker's three
    `CheckOk` shapes, and refute two of them. -/
theorem wloop_syscall_only (lim : Int) (evs : List event) (st : step_to)
    (hss : sstep wloop_segments ⟨wloop_s 5, wloop_model lim⟩ evs st) :
    evs = wloop_trace ∧ st = .SNext ⟨wloop_s6, wloop_model lim⟩ := by
  have hmat : materialize_model_accesses (wloop_model lim)
      (syscall_effect_accesses wloop_eff) = some (wloop_model lim) :=
    materialize_model_accesses_no_lazy _ _ rfl
  rcases sstep_svc_inv wloop_segments (wloop_s 5) (wloop_model lim) (BitVec.ofInt 64 64)
      evs st wloop_svc5 hss with
    ⟨eff, model', evs0, hc, H⟩ | ⟨eff, hc, he, hs⟩
  · have hcw : check_write wloop_i (fd32 (in_arg wloop_i 0)) (in_arg wloop_i 1)
        (in_arg wloop_i 2) eff (wloop_model lim) = .CheckOk model' evs0 := by
      rw [← check_syscall_write wloop_i eff (wloop_model lim) (by decide)]
      exact hc
    obtain ⟨heff, hmod, hevs⟩ := check_write_wloop_inv lim eff model' evs0 hcw
    subst heff
    subst hmod
    subst hevs
    rcases H with ⟨model'', -, rfl, hmat', rfl⟩ | ⟨-, he, hmat', -⟩ | ⟨code, hcode, -, -⟩
    · obtain rfl : model'' = wloop_model lim := by
        rw [hmat] at hmat'
        exact (Option.some.inj hmat').symm
      exact ⟨rfl, rfl⟩
    · rw [hmat] at hmat'
      exact absurd hmat' (by simp)
    · rw [show m_halted (wloop_model lim) = none from rfl] at hcode
      exact absurd hcode (by simp)
  · rw [check_syscall_write wloop_i eff (wloop_model lim) (by decide),
      check_write_wloop_walk] at hc
    cases eff with
    | mkEffectU ret ws zs us cs ci =>
      cases ws <;> cases zs <;> cases us <;> cases cs <;> dsimp only at hc
      · split at hc
        · split at hc
          · simp at hc
          · simp at hc
        · simp at hc
      all_goals simp at hc

theorem wloop_s6_only (lim : Int) (evs : List event) (st : step_to)
    (hss : sstep wloop_segments ⟨wloop_s6, wloop_model lim⟩ evs st) :
    evs = [] ∧ st = .SNext ⟨wloop_s6, wloop_model lim⟩ := by
  refine sstep_instr_only wloop_segments (with_mem wloop_s6 wloop_s6.ms_mem)
    (wloop_model lim) (with_mem wloop_s6 wloop_s6.ms_mem) rfl rfl
    (wloop_fix wloop_s6.ms_mem) evs st ?_
  rw [← with_mem_eta wloop_s6]
  exact hss

/-- The one maximal-looking path: five silent steps, the write, then
    the fixpoint. -/
theorem wloop_star (lim : Int) :
    star wloop_segments (wloop_c lim) wloop_trace ⟨wloop_s6, wloop_model lim⟩ := by
  unfold wloop_c
  exact star.step _ _ _ _ _ (wloop_instr_sstep lim 0 (by omega))
    (star.step _ _ _ _ _ (wloop_instr_sstep lim 1 (by omega))
      (star.step _ _ _ _ _ (wloop_instr_sstep lim 2 (by omega))
        (star.step _ _ _ _ _ (wloop_instr_sstep lim 3 (by omega))
          (star.step _ _ _ _ _ (wloop_instr_sstep lim 4 (by omega))
            (star.step _ _ _ _ _ (wloop_syscall_sstep lim) (star.refl _))))))

/-- Every [coexec] postcondition holds of the write-then-loop run: no
    execution ends. -/
theorem wloop_coexec_any (lim : Int) (Q : post) :
    coexec wloop_segments (wloop_c lim) Q := by
  unfold wloop_c
  apply coexec_step_only
  · exact wloop_instr_sstep lim 0 (by omega)
  · exact wloop_instr_only lim 0 (by omega)
  apply coexec_step_only
  · exact wloop_instr_sstep lim 1 (by omega)
  · exact wloop_instr_only lim 1 (by omega)
  apply coexec_step_only
  · exact wloop_instr_sstep lim 2 (by omega)
  · exact wloop_instr_only lim 2 (by omega)
  apply coexec_step_only
  · exact wloop_instr_sstep lim 3 (by omega)
  · exact wloop_instr_only lim 3 (by omega)
  apply coexec_step_only
  · exact wloop_instr_sstep lim 4 (by omega)
  · exact wloop_instr_only lim 4 (by omega)
  apply coexec_step_only
  · exact wloop_syscall_sstep lim
  · exact wloop_syscall_only lim
  exact fix_coexec_any _ _ rfl (wloop_s6_only lim) _

/-- ... and no [exec] postcondition does. -/
theorem wloop_no_exec (lim : Int) (Q : post) : ¬ exec wloop_segments (wloop_c lim) Q := by
  intro Hex
  exact fix_no_exec wloop_segments ⟨wloop_s6, wloop_model lim⟩ rfl (wloop_s6_only lim) _
    (exec_star wloop_segments (wloop_c lim) Q wloop_trace _ Hex (wloop_star lim))

theorem wloop_obs_write (lim : Int) :
    obs_trace wloop_segments (wloop_c lim) wloop_trace :=
  ⟨wloop_trace, _, wloop_star lim, is_prefix_refl _⟩

/-- The finding, pinned.  COMPARES TWO RUNS (reason 2), at either
    budget on each side.  The two runs satisfy exactly the same [coexec]
    postconditions and exactly the same [exec] postconditions ... -/
theorem loop_wloop_coexec_agree (lim1 lim2 : Int) (Q : post) :
    coexec loop_segments (loop_c lim1) Q ↔ coexec wloop_segments (wloop_c lim2) Q := by
  constructor <;> intro _
  · exact wloop_coexec_any lim2 Q
  · exact loop_coexec_any lim1 Q

theorem loop_wloop_exec_agree (lim1 lim2 : Int) (Q : post) :
    exec loop_segments (loop_c lim1) Q ↔ exec wloop_segments (wloop_c lim2) Q := by
  constructor <;> intro H
  · exact absurd H (loop_no_exec lim1 Q)
  · exact absurd H (wloop_no_exec lim2 Q)

/-- ... yet their trace sets differ, so [cosafe] tells them apart ... -/
theorem loop_wloop_cosafe_disagree (lim1 lim2 : Int) :
    ¬ (∀ P, prefix_closed P →
        (cosafe loop_segments (loop_c lim1) P ↔ cosafe wloop_segments (wloop_c lim2) P)) := by
  intro H
  obtain ⟨Hnil, -⟩ := H (fun tr => tr = []) prefix_closed_nil
  have hloop : cosafe loop_segments (loop_c lim1) (fun tr => tr = []) :=
    star_cosafe _ _ _ (fun tr c' Hstar => (fix_star_nil _ _ (loop_only lim1) tr c' Hstar).1)
  have hwl := Hnil hloop
  have hcontra := cosafe_star wloop_segments (wloop_c lim2) (fun tr => tr = []) _ _
    hwl (wloop_star lim2)
  exact absurd hcontra (by simp [wloop_trace])

theorem loop_wloop_not_trace_equiv (lim1 lim2 : Int) :
    ¬ (∀ tr, obs_trace loop_segments (loop_c lim1) tr ↔
          obs_trace wloop_segments (wloop_c lim2) tr) := by
  intro H
  exact loop_wloop_cosafe_disagree lim1 lim2
    ((obs_equiv_iff_cosafe loop_segments (loop_c lim1)
      wloop_segments (wloop_c lim2)).mp H)

/-- ... and so does the run-level equivalence, in both shapes. -/
theorem loop_wloop_not_omni_trace_equiv :
    ¬ omni_trace_equiv loop_image source_alloc_limit demo_entry
        wloop_image target_alloc_limit demo_entry demo_proc_input := by
  intro H
  refine loop_wloop_cosafe_disagree source_alloc_limit target_alloc_limit (fun P hP => ?_)
  have h := H P hP
  simpa only [omni_cosafe, loop_image, wloop_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage,
    loop_config, wloop_config] using h

theorem loop_wloop_not_omni_equiv :
    ¬ omni_equiv loop_image source_alloc_limit demo_entry
        wloop_image target_alloc_limit demo_entry demo_proc_input := by
  intro H
  rcases H with Hall | ⟨Htr, -⟩
  · simp only [omni_run, loop_image, demo_entry,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage] at Hall
    rw [loop_config] at Hall
    exact loop_no_exec source_alloc_limit _ Hall
  · exact loop_wloop_not_omni_trace_equiv Htr

theorem loop_wloop_not_equiv :
    ¬ LinuxSem.EquivalenceDefinition.Equivalence.equiv
        (run loop_image source_alloc_limit demo_entry demo_proc_input)
        (run wloop_image target_alloc_limit demo_entry demo_proc_input) := by
  intro H
  exact loop_wloop_not_omni_equiv
    ((equiv_iff loop_image source_alloc_limit demo_entry wloop_image target_alloc_limit
      demo_entry demo_proc_input).mp H)

/-- Neither image errors or leaves the model, so what separates them is
    the byte and nothing else. -/
theorem loop_wloop_never_errors (lim : Int) :
    omni_corun loop_image lim demo_entry demo_proc_input never_errors
    ∧ omni_corun wloop_image lim demo_entry demo_proc_input never_errors := by
  constructor
  · simp only [omni_corun, loop_image, demo_entry,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
    rw [loop_config]
    exact loop_coexec_any lim _
  · simp only [omni_corun, wloop_image, demo_entry,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
    rw [wloop_config]
    exact wloop_coexec_any lim _

/-- Both images put their only segment inside the first page, so the
    demo entry is valid for either. -/
theorem demo_entry_valid_loop (inp : ProcInput) (Hvalid : valid_input inp) :
    valid_entry loop_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    refine ⟨by omega, by omega, by decide⟩
  · unfold valid_brk loop_image loop_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    refine ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

theorem demo_entry_valid_wloop (inp : ProcInput) (Hvalid : valid_input inp) :
    valid_entry wloop_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    refine ⟨by omega, by omega, by decide⟩
  · unfold valid_brk wloop_image wloop_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    refine ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

theorem loop_wloop_refutes_omni_strong_universal :
    ¬ omni_strong_universal_T loop_image wloop_image := by
  intro H
  obtain ⟨-, Heq⟩ := H demo_entry demo_entry demo_proc_input
    (demo_entry_valid_loop _ demo_input_valid)
    (demo_entry_valid_wloop _ demo_input_valid)
    demo_input_valid
  exact loop_wloop_not_omni_equiv Heq
