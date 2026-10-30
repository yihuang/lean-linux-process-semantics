/-
  * OssVerify.HaltsLib — proving or refuting a halting statement about a binary

  TRUST BOUNDARY: proof library, not part of the statements.  Image-INDEPENDENT.

  A halting statement is `MustExit.must_exit_in_at_cfg` at the initial
  configuration.  That predicate is inductive, so a proof of it is a well-founded
  walk of the program, and a refutation is a finite run.  This file gives both
  their rules, in the `Common.PropExec` vocabulary (`mkst`, `getr`, `regupd`):

  - `me_step`, `me_exit`, `me_read`: an instruction, `exit_group`, and a read of
    standard input, which has exactly two answers (`StreamSim.sstep_read_inv`).
  - `runs_to_fault`: a run that deterministically faults.

  EVERY RULE HOLDS AT EVERY `SpuriousCfg`.  `read` is not in `Run.injected_table`,
  so no configuration filters it, and the other steps are not refusals at all.
  One walk therefore proves both the `forced_only_cfg` and the `may_fail_cfg`
  reading.  The price is that the rules cover only these system calls; any other
  needs its own rule, with its own answer to the filter.
-/
import Lean
import LinuxSem.Checks.SpuriousCfg
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.StreamSim
import LinuxSem.Examples.PatchClassifyDemo.Verdicts

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Bridge.Exit
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamSim
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.Checks.SpuriousCfg
open LinuxSem.Examples.PatchClassifyDemo.Verdicts

namespace LinuxSem.OssVerify.HaltsLib

/-- The FP state of a run that has executed no FP instruction: `Run`'s entry
    state, the one `PropExec.init_mkst` spells. -/
scoped instance halts_fx : FPState := fx0

/- =========================================================================
   Register values: small unsigned numbers
   ========================================================================= -/

/-- A register value that is a small unsigned number.  Every quantity a walk
    reasons about is far below `2^64`, so the arithmetic is `Nat` arithmetic and
    `omega` does it. -/
abbrev w (n : Nat) : word := BitVec.ofNat 64 n

/-- The bound under which `w` is faithful. -/
abbrev small (n : Nat) : Prop := n < 2 ^ 64

theorem w_toNat (n : Nat) (h : small n) : (w n).toNat = n := by
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem v_add_w (a b : Nat) : v_add (w a) (w b) = w (a + b) := by
  unfold v_add
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem v_sub_w (a b : Nat) (h : b ≤ a) (ha : small a) : v_sub (w a) (w b) = w (a - b) := by
  unfold v_sub
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  have hb : b < 2 ^ 64 := by omega
  omega

/-- `addi` by a non-negative immediate, as the step lemmas leave it. -/
theorem v_addi_imm (a m : Nat) (h : m < 2048) :
    v_addi (w a) (BitVec.ofNat 12 m).toInt = w (a + m) := by
  have him : (BitVec.ofNat 12 m).toInt = (m : Int) := by
    rw [BitVec.toInt_eq_toNat_of_msb]
    · simp only [BitVec.toNat_ofNat]
      omega
    · rw [BitVec.msb_eq_decide]
      simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]
      omega
  unfold v_addi
  rw [him]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem v_addi_toNat (x : word) (i : Int) (h : 0 ≤ (x.toNat : Int) + i)
    (h2 : (x.toNat : Int) + i < 2 ^ 64) :
    ((v_addi x i).toNat : Int) = (x.toNat : Int) + i := by
  unfold v_addi
  simp only [BitVec.toNat_ofInt]
  omega

/-- A register loaded with a zero-extended value. -/
theorem ofInt_natCast_w (n : Nat) : BitVec.ofInt 64 (n : Int) = w n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem c_ltu_w_t (a b : Nat) (ha : small a) (hb : small b) (h : a < b) :
    c_ltu (w a) (w b) = true := by
  simp only [c_ltu, bv_ltu, w_toNat a ha, w_toNat b hb]
  exact decide_eq_true h

theorem c_ltu_w_f (a b : Nat) (ha : small a) (hb : small b) (h : ¬ a < b) :
    c_ltu (w a) (w b) = false := by
  simp only [c_ltu, bv_ltu, w_toNat a ha, w_toNat b hb]
  exact decide_eq_false h

theorem c_eq_w_t (a b : Nat) (h : a = b) : c_eq (w a) (w b) = true := by
  subst h
  simp [c_eq, bv_eqb]

theorem c_eq_w_f (a b : Nat) (ha : small a) (hb : small b) (h : a ≠ b) :
    c_eq (w a) (w b) = false := by
  have hne : w a ≠ w b := fun he => h (by
    have := congrArg BitVec.toNat he
    rwa [w_toNat a ha, w_toNat b hb] at this)
  simp [c_eq, bv_eqb, hne]

/-- A signed comparison of two numbers below `2^63` is the unsigned one. -/
theorem c_lts_w_f (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : ¬ a < b) :
    c_lts (w a) (w b) = false := by
  have hs : ∀ n : Nat, n < 2 ^ 63 → (w n).toInt = (n : Int) := fun n hn => by
    rw [BitVec.toInt_eq_toNat_of_msb]
    · rw [w_toNat n (by omega)]
    · rw [BitVec.msb_eq_decide, w_toNat n (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
  simp only [c_lts, bv_lts, hs a ha, hs b hb]
  exact decide_eq_false (by omega)

theorem getr_regupd_same (regs : BvMap word) (r : reg) (v : word) (hr : bv_eqb r 0 = false) :
    getr (regupd regs r v) r = v := by
  simp only [getr, hr, Bool.false_eq_true, ite_false]
  exact regupd_same regs r v

theorem getr_regupd_other (regs : BvMap word) (r r' : reg) (v : word) (hr : r ≠ r') :
    getr (regupd regs r' v) r = getr regs r := by
  simp only [getr]
  rw [regupd_other regs r' v r hr]

theorem getr_x0 (regs : BvMap word) : getr regs 0#5 = w 0 := by
  simp [getr, bv_eqb]

/- Registers, by their ABI names, in the spelling the decode facts use. -/
namespace Reg
abbrev ra : reg := 0x01#5
abbrev sp : reg := 0x02#5
abbrev t0 : reg := 0x05#5
abbrev t1 : reg := 0x06#5
abbrev a0 : reg := 0x0a#5
abbrev a1 : reg := 0x0b#5
abbrev a2 : reg := 0x0c#5
abbrev a3 : reg := 0x0d#5
abbrev a4 : reg := 0x0e#5
abbrev a5 : reg := 0x0f#5
abbrev a6 : reg := 0x10#5
abbrev a7 : reg := 0x11#5
end Reg

open Reg

/- =========================================================================
   Memory
   ========================================================================= -/

/-- A byte defined in the static image reads through ANY overlay: `rdn` prefers
    the overlay and falls back to the image, so no invariant about what has been
    written is needed to know a read of the image does not fault.  What the byte
    IS depends on the overlay, and a proof of memory safety does not ask. -/
theorem rdn_one_of_rom (segs : List Segment) (mem : word → Option byte) (a : word)
    (H : (seg_rom segs a).isSome = true) : ∃ b, rdn segs mem a 1 = some [b] := by
  unfold rdn
  cases hm : mem a with
  | some b => exact ⟨b, by simp [rdn]⟩
  | none =>
      cases hs : seg_rom segs a with
      | none => rw [hs] at H; exact absurd H (by simp)
      | some b => exact ⟨b, by simp [rdn]⟩

/-- The suffix of a writable range is writable. -/
theorem wseg_ok_drop (segs : List Segment) (k : Nat) :
    ∀ (a n : Nat), wseg_ok segs (w a) (k + n) = true → wseg_ok segs (w (a + k)) n = true := by
  induction k with
  | zero => intro a n h; simpa using h
  | succ k ih =>
      intro a n h
      rw [show k + 1 + n = (k + n) + 1 by omega] at h
      unfold wseg_ok at h
      cases hseg : find_segment segs ((w a).toNat : Int) 1 with
      | none => rw [hseg] at h; exact absurd h (by simp)
      | some seg =>
          rw [hseg, Bool.and_eq_true] at h
          have e : w a + 1 = w (a + 1) := by
            apply BitVec.eq_of_toNat_eq
            have h1 : (1 : word).toNat = 1 := rfl
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]
            omega
          rw [e] at h
          have := ih (a + 1) n h.2
          rwa [show a + 1 + k = a + (k + 1) by omega] at this

/-- The store of a saved register just below the entry stack pointer. -/
theorem frame_store_ok (segs : List Segment) (ph : PhdrInfo) (sp0 : word)
    (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw)
    (hlo : (0x7fff80000000 : Int) ≤ (sp0.toNat : Int))
    (hhi : (sp0.toNat : Int) ≤ 0x800000000000) :
    store_ok segs (wrap_mem ph sp0 argv envp uid hw rnd)
      (v_addi (v_addi sp0 (-16)) 8) 8 = true := by
  have hs1 := v_addi_toNat sp0 (-16) (by omega) (by omega)
  have hs2 := v_addi_toNat (v_addi sp0 (-16)) 8 (by omega) (by omega)
  have hmax : LinuxSem.LinuxProcessSem.stack_max_size = 8 * 1024 * 1024 := rfl
  exact LinuxSem.Common.StoreOk.store_ok_wrap_window segs ph sp0 argv envp _ 8 uid hw rnd
    (by omega) (by omega)

/- =========================================================================
   What a walk carries about the model
   ========================================================================= -/

structure model_ok (model : Model) : Prop where
  halted : m_halted model = none
  lazy : m_vm_lazy model = []
  fd0 : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
    some (FdEntry.FdChannel (BitVec.ofInt 64 0))

theorem model_ok_init (reserved : List (word × word)) (brk0 mb sp : word) (lim : Int)
    (inp : ProcInput) : model_ok (init_model reserved brk0 mb sp lim inp) :=
  have H := init_M_loop reserved brk0 mb sp lim inp
  ⟨H.2.2.1, H.2.2.2, H.1⟩

theorem model_ok_take {model : Model} (k : Nat) (H : model_ok model) :
    model_ok (with_stdin (stream_take (m_stdin model) k).2 model) :=
  ⟨H.halted, by rw [m_vm_lazy_with_stdin]; exact H.lazy, H.fd0⟩

/-- The stack window of a valid entry. -/
theorem entry_sp_window (img : Image) (en : ExecEntry) (inp : ProcInput)
    (Hen : valid_entry img en inp) (Hinp : valid_input inp) :
    (0x7fff80000000 : Int) ≤ (en.en_sp.toNat : Int) ∧ (en.en_sp.toNat : Int) ≤ 0x800000000000 :=
  have Hsp := ((valid_entry_sv48 img en inp (valid_input_va_size inp Hinp)).mp Hen).1
  ⟨Hsp.1, Hsp.2.1⟩

/-- The machine state with a system call pending, as `step_ecall` leaves it. -/
abbrev pend (regs : BvMap word) (pc : word) (mem rom : word → Option byte) : machine_state :=
  { mkst regs pc mem rom with ms_svc_pending := some (getr regs a7) }

/-- `read(0, input + ..)`: what `StreamSim`'s read lemmas ask of a pending call. -/
structure read0_ready (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 buf cnt : word) : Prop where
  hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max
  hsvc : ms.ms_svc_pending = some x8
  hno : (x8.toNat : Int) = 63
  hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0
  hg1 : ms_gpr ms 1 = buf
  hg2 : ms_gpr ms 2 = cnt
  hw : ∃ v, read_bytes_map (ms_writable_byte segs ms) buf cnt = some v
  haok : access_okb buf (cnt.toNat : Int) = true

/-- The registers and the writable range of a pending `read(0, buf, cnt)`. -/
structure read_args (segs : List Segment) (regs : BvMap word) (buf cnt : Nat) : Prop where
  h7 : getr regs a7 = w 63
  h0 : getr regs a0 = w 0
  h1 : getr regs a1 = w buf
  h2 : getr regs a2 = w cnt
  hcnt : 0 < cnt ∧ cnt ≤ 131072
  hbuf : buf + cnt ≤ 0x800000000000
  hwr : wseg_ok segs (w buf) cnt = true

theorem read_args.ready {segs : List Segment} {regs : BvMap word} {buf cnt : Nat}
    (H : read_args segs regs buf cnt) (pc : word) (mem rom : word → Option byte) (model : Model) :
    read0_ready segs (pend regs pc mem rom) model (w 63) (w buf) (w cnt) := by
  have hc : (w cnt).toNat = cnt := w_toNat _ (by have := H.hcnt.2; omega)
  have hb : (w buf).toNat = buf := w_toNat _ (by have := H.hbuf; omega)
  have hmax : rw_bytes_max = 131072 := rfl
  have hts : TASK_SIZE = 0x800000000000 := rfl
  have hcn := H.hcnt
  have hbf := H.hbuf
  refine ⟨?_, ?_, by decide, ?_, H.h1, H.h2, ?_, ?_⟩
  · rw [hc]; omega
  · show some (getr regs a7) = some (w 63)
    rw [H.h7]
  · show getr regs a0 = _
    rw [H.h0]; rfl
  · refine wseg_ok_wdef segs _ _ _ ?_
    rw [show word_to_nat (w cnt) = cnt from hc]
    exact H.hwr
  · simp only [access_okb, Bool.and_eq_true, decide_eq_true_eq]
    rw [hc, hb]
    omega

/- =========================================================================
   Proving: the walk's rules
   ========================================================================= -/

section Rules

variable {cfg : SpuriousCfg} {segs : List Segment} {S : List word}
  {regs : BvMap word} {pc : word} {mem rom : word → Option byte} {model : Model}

/-- The claim at a machine state and a model. -/
abbrev ME (cfg : SpuriousCfg) (segs : List Segment) (S : List word)
    (ms : machine_state) (model : Model) : Prop :=
  must_exit_in_at_cfg cfg segs S ⟨ms, model⟩

/-- An instruction that steps: its one successor carries the claim. -/
theorem me_step (Hm : model_ok model) {ms' : machine_state}
    (hstep : RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineOk ms')
    (h : ME cfg segs S ms' model) : ME cfg segs S (mkst regs pc mem rom) model := by
  have hsvc : (mkst regs pc mem rom).ms_svc_pending = none := rfl
  have hacc : mi_account_step segs (mkst regs pc mem rom) model = .MachineOk (ms', model) := by
    rw [mi_account_step_no_lazy segs _ model Hm.lazy, hstep]
  refine must_exit_in_at_cfg.running _ Hm.halted
    ⟨[], .SNext ⟨ms', model⟩, sstep_cfg.instr _ model ms' model Hm.halted hsvc hacc⟩ ?_ ?_
  · intro evs herr
    obtain ⟨-, hst⟩ := sstep_cfg_instr_only segs cfg _ model ms' Hm.lazy hsvc hstep evs .SError herr
    cases hst
  · intro evs c' hss
    obtain ⟨-, hst⟩ := sstep_cfg_instr_only segs cfg _ model ms' Hm.lazy hsvc hstep evs (.SNext c') hss
    cases hst
    exact h

/-- `exit_group` with an allowed masked status. -/
theorem me_exit {n : Nat} (Hm : model_ok model)
    (h7 : getr regs a7 = w 94) (h0 : getr regs a0 = w n)
    (hin : (w n &&& BitVec.ofInt 64 255 : word) ∈ S) :
    ME cfg segs S (pend regs pc mem rom) model := by
  have hsvc : (pend regs pc mem rom).ms_svc_pending = some (w 94) := by
    show some (getr regs a7) = _
    rw [h7]
  have hno : exit_number (sys_input segs (pend regs pc mem rom) (w 94)).in_sysno :=
    Or.inr (show ((w 94).toNat : Int) = 94 by decide)
  have hcode : ms_gpr (pend regs pc mem rom) 0 &&& BitVec.ofInt 64 255
      = w n &&& BitVec.ofInt 64 255 := by
    show getr regs a0 &&& _ = _
    rw [h0]
  have hspec := exit_spec_at segs (pend regs pc mem rom) model (w 94) hno
  refine must_exit_in_at_cfg.running _ Hm.halted
    ⟨_, _, sstep_cfg.exit _ model (w 94) (mkEffect (BitVec.ofInt 64 0) [] [])
      (with_halted (in_arg (sys_input segs _ (w 94)) 0 &&& BitVec.ofInt 64 255) model) []
      (w n &&& BitVec.ofInt 64 255) Hm.halted hsvc hspec
      (by rw [m_halted_with_halted, sys_input_arg0, hcode]) (by rw [m_killed_with_halted])⟩ ?_ ?_
  · intro evs herr
    obtain ⟨m', hst, -, -⟩ := sstep_cfg_exit_only segs cfg _ model _ _ hsvc hno hcode evs .SError herr
    cases hst
  · intro evs c' hss
    obtain ⟨m', hst, hhalt, hnk⟩ :=
      sstep_cfg_exit_only segs cfg _ model _ _ hsvc hno hcode evs (.SNext c') hss
    cases hst
    exact must_exit_in_at_cfg.halted _ _ hhalt hin hnk

/-- `read` is not an injected arm, so no configuration filters its answers. -/
theorem read_not_spurious (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (hno : (i.in_sysno.toNat : Int) = 63) :
    ¬ spurious_refusal_cfg cfg i m eff := by
  rintro ⟨hoff, -, -⟩
  have hn : i.in_sysno.toNat = 63 := by omega
  have harm : injected_arm 63 = none := by decide
  simp only [injected_family_off, hn, harm] at hoff
  exact absurd hoff (by simp)

/-- The end-of-input answer of a pending `read`, as a filtered step. -/
theorem read_eof_sstep {ms : machine_state} {x8 buf cnt : word} (Hm : model_ok model)
    (R : read0_ready segs ms model x8 buf cnt) (Heof : m_stdin model 0 = none) :
    sstep_cfg segs cfg ⟨ms, model⟩ []
      (.SNext ⟨advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 0)), model⟩) := by
  obtain ⟨v, hv⟩ := R.hw
  rw [← apply_effect_no_write]
  refine sstep_cfg.syscall ms model x8 _ model model [] Hm.halted R.hsvc ?_
    (read_not_spurious _ _ _ R.hno) Hm.halted (materialize_model_accesses_no_lazy model _ Hm.lazy)
  exact read0_ok_eof cnt R.hcnt segs ms x8 model v R.hno Hm.fd0 Heof R.hg0 R.hg2
    (by rw [R.hg1]; exact hv) (by rw [R.hg1]; exact R.haok)

/-- `read(0, buf, cnt)`: one continuation for end of input, and one for every
    nonempty block of at most `cnt` bytes the stream can deliver. -/
theorem me_read {buf cnt : Nat} (Hm : model_ok model) (A : read_args segs regs buf cnt)
    (Heof : ME cfg segs S (mkst (regupd regs a0 (w 0)) (pc + BitVec.ofInt 64 4) mem rom) model)
    (Hbytes : ∀ bs : List byte, 1 ≤ bs.length → bs.length ≤ cnt →
      ME cfg segs S (mkst (regupd regs a0 (w bs.length)) (pc + BitVec.ofInt 64 4)
          (write_to_mem mem (w buf) bs) rom)
        (with_stdin (stream_take (m_stdin model) bs.length).2 model)) :
    ME cfg segs S (pend regs pc mem rom) model := by
  have R := A.ready pc mem rom model
  obtain ⟨v, hv⟩ := R.hw
  have hc : (w cnt).toNat = cnt := w_toNat _ (by have := A.hcnt.2; omega)
  have hprog : ∃ evs st, sstep_cfg segs cfg ⟨pend regs pc mem rom, model⟩ evs st := by
    cases hs : m_stdin model 0 with
    | none => exact ⟨_, _, read_eof_sstep Hm R hs⟩
    | some b0 =>
        have htake : (stream_take (m_stdin model) 1).1 = [b0] := by simp only [stream_take, hs]
        have hspec := read0_ok_bytes (w cnt) R.hcnt segs _ (w 63) model v [b0] R.hno Hm.fd0 R.hg0
          R.hg2 (by rw [R.hg1]; exact hv) (by rw [R.hg1]; exact R.haok) (by simp)
          (by have := A.hcnt.1; simp only [List.length_cons, List.length_nil]; omega) htake
        exact ⟨_, _, sstep_cfg.syscall _ model _ _ _ _ _ Hm.halted R.hsvc hspec
          (read_not_spurious _ _ _ R.hno) Hm.halted
          (materialize_model_accesses_no_lazy _ _ (model_ok_take _ Hm).lazy)⟩
  refine must_exit_in_at_cfg.running _ Hm.halted hprog ?_ ?_
  · intro evs herr
    rcases sstep_read_inv _ R.hcnt segs _ model _ _ v evs .SError Hm.halted Hm.lazy Hm.fd0 R.hsvc
        R.hno R.hg0 R.hg1 R.hg2 hv R.haok (sstep_cfg_sub segs cfg _ _ _ herr) with
      ⟨-, -, hst⟩ | ⟨bs, -, -, -, -, hst⟩ <;> cases hst
  · intro evs c' hss
    rcases sstep_read_inv _ R.hcnt segs _ model _ _ v evs (.SNext c') Hm.halted Hm.lazy Hm.fd0
        R.hsvc R.hno R.hg0 R.hg1 R.hg2 hv R.haok (sstep_cfg_sub segs cfg _ _ _ hss) with
      ⟨-, -, hst⟩ | ⟨bs, hlo, hhi, -, -, hst⟩
    · cases hst
      exact Heof
    · cases hst
      exact Hbytes bs (by omega) (by rw [hc] at hhi; omega)

end Rules

/- =========================================================================
   Refuting: a run that deterministically faults
   ========================================================================= -/

/-- `c` runs, with no choice along the way, to an instruction that faults.  One
    judgment gives both things a refutation needs: the conclusion is false
    (`runs_to_fault_not_must_exit`), and the budget premise holds, because a run
    that makes no memory request is never refused one
    (`runs_to_fault_not_refused`). -/
inductive runs_to_fault (segs : List Segment) : config → Prop where
  | fault (ms : machine_state) (model : Model) (Hm : model_ok model)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineFault) :
      runs_to_fault segs ⟨ms, model⟩
  | instr (ms ms' : machine_state) (model : Model) (Hm : model_ok model)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (h : runs_to_fault segs ⟨ms', model⟩) :
      runs_to_fault segs ⟨ms, model⟩
  | read_eof (ms : machine_state) (model : Model) (x8 buf cnt : word) (Hm : model_ok model)
      (R : read0_ready segs ms model x8 buf cnt)
      (Heof : m_stdin model 0 = none)
      (h : runs_to_fault segs ⟨advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 0)), model⟩) :
      runs_to_fault segs ⟨ms, model⟩

theorem runs_to_fault_not_must_exit (cfg : SpuriousCfg) (segs : List Segment) (S : List word)
    (c : config) (H : runs_to_fault segs c) : ¬ must_exit_in_at_cfg cfg segs S c := by
  induction H with
  | fault ms model Hm hsvc hstep =>
      intro hme
      cases hme with
      | halted _ _ hh' _ _ => rw [Hm.halted] at hh'; exact absurd hh' (by simp)
      | running _ _ _ hnoerr _ =>
          refine hnoerr [] (sstep_cfg.instr_fault ms model Hm.halted hsvc ?_)
          rw [mi_account_step_no_lazy segs ms model Hm.lazy, hstep]
  | instr ms ms' model Hm hsvc hstep _ ih =>
      intro hme
      cases hme with
      | halted _ _ hh' _ _ => rw [Hm.halted] at hh'; exact absurd hh' (by simp)
      | running _ _ _ _ hnext =>
          refine ih (hnext [] ⟨ms', model⟩ (sstep_cfg.instr ms model ms' model Hm.halted hsvc ?_))
          rw [mi_account_step_no_lazy segs ms model Hm.lazy, hstep]
  | read_eof ms model x8 buf cnt Hm R Heof _ ih =>
      intro hme
      cases hme with
      | halted _ _ hh' _ _ => rw [Hm.halted] at hh'; exact absurd hh' (by simp)
      | running _ _ _ _ hnext => exact ih (hnext [] _ (read_eof_sstep Hm R Heof))

theorem runs_to_fault_not_refused (segs : List Segment) (c : config)
    (H : runs_to_fault segs c) : ¬ reaches_budget_refused segs c := by
  induction H with
  | fault ms model Hm hsvc hstep =>
      rintro ⟨tr, c', hstar, hb⟩
      have hlazy := Hm.lazy
      cases hstar with
      | refl => exact budget_refused_at_no_lazy_instr segs ms model hlazy hsvc hb
      | step _ evs c2 _ _ h1 _ => cases h1 <;> simp_all [mi_account_step_no_lazy]
  | instr ms ms' model Hm hsvc hstep _ ih =>
      rintro ⟨tr, c', hstar, hb⟩
      cases hstar with
      | refl => exact budget_refused_at_no_lazy_instr segs ms model Hm.lazy hsvc hb
      | step _ evs c2 tr' _ h1 h2 =>
          obtain ⟨-, hst⟩ := sstep_cfg_instr_only segs may_fail_cfg ms model ms' Hm.lazy hsvc hstep
            evs (.SNext c2) ((sstep_cfg_may_fail segs _ _ _).mp h1)
          cases hst
          exact ih ⟨tr', c', h2, hb⟩
  | read_eof ms model x8 buf cnt Hm R Heof _ ih =>
      obtain ⟨v, hv⟩ := R.hw
      rintro ⟨tr, c', hstar, hb⟩
      cases hstar with
      | refl =>
          have hn : (sys_input segs ms x8).in_sysno.toNat = 63 := by
            have := R.hno
            show x8.toNat = 63
            omega
          have hfree : alloc_budget_refused_b (sys_input segs ms x8) model = false := by
            simp [alloc_budget_refused_b, hn]
          have hiff := budget_refused_at_no_lazy_syscall segs ms model x8 Hm.halted R.hsvc (by
            intro eff m' evs hspec
            rcases read0_ok_inv cnt R.hcnt segs ms x8 model buf v eff m' evs R.hno Hm.fd0 R.hg0
                R.hg1 R.hg2 hv R.haok hspec with ⟨-, -, hm, -⟩ | ⟨bs, -, -, -, -, hm, -⟩
            · rw [hm]; exact Hm.lazy
            · rw [hm, m_vm_lazy_with_stdin]; exact Hm.lazy)
          rw [hiff, hfree] at hb
          exact absurd hb (by simp)
      | step _ evs c2 tr' _ h1 h2 =>
          rcases sstep_read_inv cnt R.hcnt segs ms model buf x8 v evs (.SNext c2) Hm.halted Hm.lazy
              Hm.fd0 R.hsvc R.hno R.hg0 R.hg1 R.hg2 hv R.haok h1 with
            ⟨-, -, hst⟩ | ⟨bs, hlo, -, hpre, -, -⟩
          · cases hst
            exact ih ⟨tr', c', h2, hb⟩
          · exfalso
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show bs.length ≠ 0 by omega)
            rw [hk] at hpre
            simp only [stream_take, Heof] at hpre
            rw [← hpre] at hk
            simp at hk

/-- The rule for an instruction on the refuting side, in `me_step`'s shape. -/
theorem rf_step {segs : List Segment} {regs : BvMap word} {pc : word}
    {mem rom : word → Option byte} {model : Model} (Hm : model_ok model) {ms' : machine_state}
    (hstep : RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineOk ms')
    (h : runs_to_fault segs ⟨ms', model⟩) : runs_to_fault segs ⟨mkst regs pc mem rom, model⟩ :=
  runs_to_fault.instr _ ms' model Hm rfl hstep h

/-- A pending `read` at end of input, in `me_read`'s shape. -/
theorem rf_read_eof {segs : List Segment} {regs : BvMap word} {pc : word}
    {mem rom : word → Option byte} {model : Model} {buf cnt : Nat} (Hm : model_ok model)
    (A : read_args segs regs buf cnt) (Heof : m_stdin model 0 = none)
    (h : runs_to_fault segs ⟨mkst (regupd regs a0 (w 0)) (pc + BitVec.ofInt 64 4) mem rom, model⟩) :
    runs_to_fault segs ⟨pend regs pc mem rom, model⟩ :=
  runs_to_fault.read_eof _ model _ _ _ Hm (A.ready pc mem rom model) Heof h

/-- `lbu` of a byte no mapping holds faults. -/
theorem step_lbu_fault (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ1 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 1 = none) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineFault := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 1 = none := by
    rw [hba, ov_rdn]; exact Hread
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  rw [hov]

/- =========================================================================
   The walk's tactics
   ========================================================================= -/

/-- Normalise register values: read them back through the `regupd`s of the block,
    and do the small-number arithmetic. -/
macro "wnv" : tactic =>
  `(tactic| simp (disch := first | decide | omega) only
      [getr_regupd_same, getr_regupd_other, getr_x0, v_add_w, v_sub_w, v_addi_imm,
       ofInt_natCast_w, BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceSub, Nat.zero_add,
       Nat.add_zero, *])

/-- Apply the instruction rule of whichever judgment the goal is.  It reads the
    goal's head rather than trying both, because a failed attempt still elaborates
    the step lemma, whose fetch and decode facts are the expensive part. -/
elab "wrule " h:term : tactic => do
  let tgt ← Lean.Meta.whnfR (← Lean.Elab.Tactic.getMainTarget)
  Lean.Elab.Tactic.evalTactic (← if tgt.isAppOf ``runs_to_fault then
    `(tactic| refine rf_step (by assumption) $h ?_)
  else
    `(tactic| refine me_step (by assumption) $h ?_))

/-- Drop the `if rd = x0` every step lemma leaves in its register file. -/
macro "wif" : tactic =>
  `(tactic| simp only [show ∀ r : reg, bv_eqb r 0 = (r == 0) from fun _ => rfl,
      reduceIte, Bool.false_eq_true, Bool.true_eq_false, BitVec.reduceBEq])

/-- An instruction, by its step lemma, fetch fact and decode fact. -/
macro "wst " l:term ", " F:term ", " D:term : tactic =>
  `(tactic| (wrule ($l (Hfetch := $F) (Hecall := rfl) (Hdecode := $D) ..); wif; try wnv))

/-- `ecall`. -/
macro "wecall " F:term : tactic =>
  `(tactic| wrule (step_ecall (Hfetch := $F) (Hecall := rfl) ..))

/-- `lbu` of a byte `hb`-like hypotheses say reads as `b`. -/
macro "wlbu " b:term ", " F:term ", " D:term : tactic =>
  `(tactic| (wrule (step_lbu (b := $b) (Hfetch := $F) (Hecall := rfl) (Hdecode := $D)
      (Hread := by wnv) ..); wif; try wnv))

/-- Close a branch condition over small numbers. -/
macro "wcmp" : tactic =>
  `(tactic| first
    | exact c_ltu_w_t _ _ (by omega) (by omega) (by omega)
    | exact c_ltu_w_f _ _ (by omega) (by omega) (by omega)
    | exact c_eq_w_t _ _ (by omega)
    | exact c_eq_w_f _ _ (by omega) (by omega) (by omega)
    | exact c_lts_w_f _ _ (by omega) (by omega) (by omega))

/-- A branch, by the step lemma for the direction taken. -/
macro "wbr " l:term ", " F:term ", " D:term : tactic =>
  `(tactic| wrule ($l (Hfetch := $F) (Hecall := rfl) (Hdecode := $D)
      (Hc := by (try wnv); wcmp) ..))

end LinuxSem.OssVerify.HaltsLib
