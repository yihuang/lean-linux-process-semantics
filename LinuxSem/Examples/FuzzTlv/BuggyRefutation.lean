/-
  * Examples.FuzzTlv.BuggyRefutation — the build without the fixes really fails

  PROOF-SIDE FILE (not part of the trusted statements).

  A proof that no input makes a build fail says little unless the same statement
  can be false, so this file refutes it for the source built without `-DFIXED`.

  THE COUNTEREXAMPLE IS EMPTY STANDARD INPUT.  The driver reads 0 bytes, and with no
  check of `n` against the header it calls the target with `size = n - 6`, which
  underflows to `2^64 - 6`.  The buffer is zero-filled, so every record has `len = 0`
  and the walk advances 2 bytes at a time, off the end of the buffer, until the load
  of `data[off + 1]` at `off = 250` reads `0x1004001`.  No segment maps it.

  The entry is not concrete: it comes from `image_brk_satisfiable_entry`, and the
  walk uses only the stack window.
-/
import LinuxSem.OssVerify.HaltsLib
import LinuxSem.Checks.Examples
import LinuxSem.Examples.FuzzTlv.Images
import LinuxSem.Examples.FuzzTlv.Statements
import LinuxSem.Examples.FuzzTlv.BuggyFacts

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamSim
open LinuxSem.Checks.Examples
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.OssVerify.Shapes
open LinuxSem.OssVerify.Images
open LinuxSem.OssVerify.HaltsLib
open LinuxSem.OssVerify.HaltsLib.Reg
open LinuxSem.Examples.FuzzTlv.Images
open LinuxSem.Examples.FuzzTlv.BuggyFacts

namespace LinuxSem.Examples.FuzzTlv.BuggyRefutation

abbrev RF (ms : machine_state) (model : Model) : Prop :=
  runs_to_fault buggy_segs ⟨ms, model⟩

/-- `size` as the driver computes it for an empty input. -/
local notation "HUGE" => (18446744073709551610 : Nat)

/-- The buffer, zero-filled because nothing has been read into it. -/
theorem input_rom_zero :
    ∀ k, k < 256 → seg_rom buggy_segs (w (0x1003f00 + k)) = some 0#8 := by
  decide

/-- The first address the walk reads past the end of the image. -/
theorem unmapped_rom : seg_rom buggy_segs (w 0x1004001) = none := by
  decide

theorem input_writable : wseg_ok buggy_segs (w 0x1003f00) 256 = true := by
  decide

/-- `head`, walking zero-length records until the load that faults. -/
theorem walk {mem rom : word → Option byte} {model : Model} (Hm : model_ok model)
    (Hz : ∀ k, k < 256 → rdn buggy_segs mem (w (0x1003f00 + k)) 1 = some [0#8])
    (Hf : rdn buggy_segs mem (w 0x1004001) 1 = none) :
    ∀ (fuel : Nat) (regs : BvMap word) (off : Nat), off + 2 * fuel = 250 →
      getr regs a1 = w HUGE → getr regs a3 = w 0x1003f07 → getr regs a5 = w 1 →
      getr regs t0 = w off →
      RF (mkst regs (BitVec.ofInt 64 0x10011bc) mem rom) model := by
  intro fuel
  induction fuel with
  | zero =>
    intro regs off ho h1 h3 h5 ht0
    obtain rfl : off = 250 := by omega
    wst step_add, F_10011bc, D_00568833
    exact runs_to_fault.fault _ model Hm rfl
      (step_lbu_fault _ _ _ _ _ _ _ _ _ F_10011c0 rfl D_00084803 (by wnv))
  | succ fuel ih =>
    intro regs off ho h1 h3 h5 ht0
    wst step_add, F_10011bc, D_00568833
    have hb := Hz (7 + off) (by omega)
    rw [show 0x1003f00 + (7 + off) = 0x1003f07 + off by omega] at hb
    wlbu 0#8, F_10011c0, D_00084803
    wst step_addi, F_10011c4, D_00228893
    wbr step_beq_tk, F_10011c8, D_fe0804e3
    wst step_add, F_10011b0, D_010882b3
    wst step_sub, F_10011b4, D_40558833
    wbr step_bgeu_ft, F_10011b8, D_0307fe63
    exact ih _ (off + 2) (by omega) (by wnv) (by wnv) (by wnv) (by wnv)

/-- From `_start`, on empty standard input. -/
theorem from_start {sp0 : word} {mem rom : word → Option byte} {regs : BvMap word} {model : Model}
    (hlo : (0x7fff80000000 : Int) ≤ (sp0.toNat : Int))
    (hhi : (sp0.toNat : Int) ≤ 0x800000000000)
    (Hm : model_ok model) (Heof : m_stdin model 0 = none)
    (hsp : getr regs sp = sp0)
    (hstore : store_ok buggy_segs mem (v_addi (v_addi sp0 (-16)) 8) 8 = true)
    (Hlow : ∀ x : Nat, x < 0x2000000 → mem (w x) = none) :
    RF (mkst regs (BitVec.ofInt 64 0x100120c) mem rom) model := by
  have hi : (0xff0#12 : BitVec 12).toInt = -16 := by decide
  have ha8 : (0x008#12 : BitVec 12).toInt = 8 := by decide
  have hlui : v_lui (zshiftl (0x01003#20 : BitVec 20).toInt 12) = w 0x1003000 := by decide
  have hunder : v_addi (w 0) (0xffa#12 : BitVec 12).toInt = w HUGE := by decide
  wst step_addi, F_100120c, D_ff010113
  wrule (step_sd_val (Hfetch := F_1001210) (Hecall := rfl) (Hdecode := D_00113423)
    (Hok := by wnv) ..)
  wnv
  -- the store is far above the buffer, so the buffer still reads from the image
  have hs1 := v_addi_toNat sp0 (-16) (by omega) (by omega)
  have hs2 := v_addi_toNat (v_addi sp0 (-16)) 8 (by omega) (by omega)
  have Hrd : ∀ x : Nat, x < 0x2000000 →
      rdn buggy_segs (wbytes mem (v_addi (v_addi sp0 (-16)) 8)
        (word_to_le_bytes 8 (getr regs ra))) (w x) 1
      = match seg_rom buggy_segs (w x) with
        | some b => some [b]
        | none => none := by
    intro x hx
    rw [rdn_wbytes_below _ _ _ _ _ _
      (by rw [w_toNat x (by omega)]; omega) (by rw [length_N_to_le_bytes]; omega)]
    simp only [rdn, Hlow x hx]
    cases seg_rom buggy_segs (w x) <;> rfl
  have Hz := fun k (hk : k < 256) => (Hrd (0x1003f00 + k) (by omega)).trans
    (by rw [input_rom_zero k hk])
  have Hf := (Hrd 0x1004001 (by omega)).trans (by rw [unmapped_rom])
  generalize wbytes mem (v_addi (v_addi sp0 (-16)) 8) (word_to_le_bytes 8 (getr regs ra))
    = mem' at Hz Hf ⊢
  wst step_addi, F_1001214, D_00000693
  wst step_lui, F_1001218, D_01003737
  wst step_addi, F_100121c, D_00070713
  wst step_addi, F_1001220, D_10000793
  wst step_addi, F_1001224, D_03f00893
  wst step_add, F_1001228, D_00d70533
  wst step_sub, F_100122c, D_40d78633
  wst step_addi, F_1001230, D_7ff50513
  wst step_addi, F_1001234, D_70150593
  wst step_addi, F_1001238, D_00000513
  wecall F_100123c
  refine rf_read_eof (buf := 0x1003f00) (cnt := 256) Hm
    ⟨by wnv, by wnv, by wnv, by wnv, by decide, by decide, input_writable⟩ Heof ?_
  -- r = 0: past the `r < 0` test, and on to the call, with no check of `n`
  wbr step_blt_ft, F_1001240, D_02054263
  wbr step_beq_tk, F_1001244, D_02050a63
  wst step_addi, F_1001278, D_ffa68593
  wst step_addi, F_100127c, D_7ff70513
  wst step_addi, F_1001280, D_70750513
  wst step_auipc, F_1001284, D_00000097
  wst step_jalr_gen, F_1001288, D_f0c080e7
  -- the target, believing it has `2^64 - 6` bytes
  wst step_addi, F_1001190, D_00200613
  wbr step_bltu_ft, F_1001194, D_04c5ec63
  wst step_addi, F_1001198, D_00000293
  wst step_addi, F_100119c, D_00000613
  wst step_addi, F_10011a0, D_00150693
  wst step_addi, F_10011a4, D_00250713
  wst step_addi, F_10011a8, D_00100793
  wrule (step_jal_x0 (Hfetch := F_10011ac) (Hecall := rfl) (Hdecode := D_0100006f) ..)
  exact walk Hm Hz Hf 125 _ 0 (by decide) (by wnv) (by wnv) (by wnv) (by wnv)

/-- The whole counterexample: at every valid entry, on `demo_proc_input` (empty
    standard input), the run deterministically faults. -/
theorem buggy_faults (lim : Int) (en : ExecEntry) (Hen : valid_entry buggy en demo_proc_input) :
    runs_to_fault buggy_segs
      (init_config buggy_segs buggy_mem.init_pc buggy_mem.phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw lim demo_proc_input) := by
  obtain ⟨sp0, brk0, mbase, rnd⟩ := en
  obtain ⟨hlo, hhi⟩ : (0x7fff80000000 : Int) ≤ (sp0.toNat : Int)
      ∧ (sp0.toNat : Int) ≤ 0x800000000000 :=
    entry_sp_window buggy _ _ Hen demo_input_valid
  show runs_to_fault buggy_segs
    ⟨init_machine_state buggy_segs buggy_mem.init_pc buggy_mem.phdrs sp0 rnd
        demo_proc_input.in_argv demo_proc_input.in_envp
        demo_proc_input.in_uid demo_proc_input.in_hwcap,
     init_model (segments_reserved buggy_segs) brk0 mbase sp0 lim demo_proc_input⟩
  rw [init_mkst]
  have hmax : stack_max_size = 8 * 1024 * 1024 := rfl
  refine from_start hlo hhi (model_ok_init _ _ _ _ _ _) rfl (getr_regupd_same _ _ _ (by decide))
    (frame_store_ok _ _ _ _ _ _ _ _ hlo hhi) ?_
  intro x hx
  have hxw : (w x).toNat = x := w_toNat x (by omega)
  simp only [wrap_mem, stack_to_mem]
  rw [ite_eq_right_iff.mpr (fun h => by rw [hxw] at h; omega)]
  simp only [hxw]
  apply ite_eq_right_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  intro h
  omega

theorem buggy_entry : ∃ en, valid_entry buggy en demo_proc_input :=
  image_brk_satisfiable_entry buggy _ demo_input_valid buggy_wf.2.2

theorem buggy_halts_refuted : ¬ Statements.halts buggy := by
  intro H
  obtain ⟨en, Hen⟩ := buggy_entry
  have Hrun := buggy_faults budgets.lim_source en Hen
  exact runs_to_fault_not_must_exit forced_only_cfg _ ok_or_refused _ Hrun
    (H en _ Hen demo_input_valid fun Href =>
      runs_to_fault_not_refused _ _ Hrun (reaches_budget_refused_cfg_sub _ _ _ Href))

theorem buggy_halts_may_fail_refuted : ¬ Statements.halts_may_fail buggy := by
  intro H
  obtain ⟨en, Hen⟩ := buggy_entry
  exact runs_to_fault_not_must_exit may_fail_cfg _ ok_or_refused _
    (buggy_faults source_alloc_limit en Hen) (H en _ Hen demo_input_valid)

end LinuxSem.Examples.FuzzTlv.BuggyRefutation
