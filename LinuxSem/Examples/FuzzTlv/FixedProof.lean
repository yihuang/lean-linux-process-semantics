/-
  * Examples.FuzzTlv.FixedProof — no input makes the fixed build fail

  PROOF-SIDE FILE (not part of the trusted statements).

  ** The program, as the compiler left it

      _start     0x100121c  sp -= 16; save ra; n = 0
      read_loop  0x1001238  r = read(0, input + n, 256 - n)
                 0x1001250  r < 0: exit(2).  r = 0: to eof.  n += r.
                            n = 256: exit(2).  otherwise back to read_loop
      eof        0x1001288  n < 6: exit(2).  otherwise call the target
      target     0x1001190  size < 2: return 0.  off = 0
      head       0x10011bc  len = data[off + 1]
                            len > size - (off + 2): return -1
                            len = 0: to next
      sum_loop   0x10011e0  for each i < len: read data[off + 2 + i]
      next       0x10011b0  off = off + 2 + len
                            size - off <= 1: return.  otherwise to head
      after_call 0x10012b8  exit(0)

  The compiler saw that the target only returns 0 or -1 and folded the driver's
  status 78 away, so the call's result is not read at all.

  ** Termination

  - `read_loop`: every answer of `read` is end of input or at least one byte, so
    `256 - n` falls.  This is what makes the proof hold for an INFINITE stdin.
  - `head`: `off` grows by at least 2 and stays at most `size`.
  - `sum_loop`: the cursor `t1` grows to `t0`.

  ** Why no read faults

  Every `lbu` reads below `data + size = input + n`, with `n < 256`, so below the
  end of the mapped page.  The two `FIXED` lines of the source are what make this
  true: `n < 6` refuses a short input, and `len > size - off` refuses a record that
  runs past the data.
-/
import LinuxSem.OssVerify.HaltsLib
import LinuxSem.Examples.FuzzTlv.Images
import LinuxSem.Examples.FuzzTlv.Statements
import LinuxSem.Examples.FuzzTlv.FixedFacts

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamSim
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.OssVerify.Shapes
open LinuxSem.OssVerify.HaltsLib
open LinuxSem.OssVerify.HaltsLib.Reg
open LinuxSem.Examples.FuzzTlv.Images
open LinuxSem.Examples.FuzzTlv.FixedFacts

namespace LinuxSem.Examples.FuzzTlv.FixedProof

/-- The claim, about this image. -/
abbrev PM (cfg : SpuriousCfg) (ms : machine_state) (model : Model) : Prop :=
  ME cfg plain_segs ok_or_refused ms model

variable {cfg : SpuriousCfg} {regs : BvMap word} {mem rom : word → Option byte} {model : Model}

/- The first byte of the driver's buffer, and its size.  Notation rather than
   definitions, because `omega` treats a definition as an opaque atom. -/
local notation "input_base" => (0x1003f00 : Nat)
local notation "BUF" => (256 : Nat)

theorem input_rom_defined :
    ∀ k, k < BUF → (seg_rom plain_segs (w (input_base + k))).isSome = true := by
  decide

theorem input_writable : wseg_ok plain_segs (w input_base) BUF = true := by
  decide

/-- Any byte of the buffer reads. -/
theorem rdn_buf (mem : word → Option byte) (x : Nat)
    (hlo : input_base ≤ x) (hhi : x < input_base + BUF) :
    ∃ b, rdn plain_segs mem (w x) 1 = some [b] := by
  have h := input_rom_defined (x - input_base) (by omega)
  rw [show input_base + (x - input_base) = x by omega] at h
  exact rdn_one_of_rom _ _ _ h

/- =========================================================================
   The target's exits
   ========================================================================= -/

/-- `after_call`: the driver's exit(0). -/
theorem after_call_exits (Hm : model_ok model) :
    PM cfg (mkst regs (BitVec.ofInt 64 0x10012b8) mem rom) model := by
  wst step_addi, F_10012b8, D_05e00893
  wst step_addi, F_10012bc, D_00000593
  wst step_addi, F_10012c0, D_00000613
  wst step_addi, F_10012c4, D_00000513
  wecall F_10012c8
  exact me_exit (n := 0) Hm (by wnv) (by wnv) (by decide)

/-- `ret`, with the return address the call left. -/
theorem me_ret {pc : word} (Hm : model_ok model) (hra : getr regs ra = w 0x10012b8)
    (F : fetch_word plain_segs pc = some 0x00008067) :
    PM cfg (mkst regs pc mem rom) model := by
  wst step_jalr_gen, F, D_00008067
  exact after_call_exits Hm

/-- The record walk finished: compute the sum's verdict, and return it. -/
theorem done_block (Hm : model_ok model) (hra : getr regs ra = w 0x10012b8) :
    PM cfg (mkst regs (BitVec.ofInt 64 0x1001204) mem rom) model := by
  wst step_lui, F_1001204, D_deadc537
  wst step_addiw, F_1001208, D_eef5051b
  wst step_xor, F_100120c, D_00a64533
  wst step_sltu, F_1001210, D_00a03533
  wst step_addi, F_1001214, D_fff50513
  exact me_ret Hm (by wnv) F_1001218

/- =========================================================================
   The record walk
   ========================================================================= -/

/-- The registers the walk does not change: the arguments, the two cached
    `data + 1`, `data + 2`, the constant 1, and the return address. -/
structure tgt_regs (regs : BvMap word) (size : Nat) : Prop where
  a0 : getr regs a0 = w 0x1003f06
  a1 : getr regs a1 = w size
  a3 : getr regs a3 = w 0x1003f07
  a4 : getr regs a4 = w 0x1003f08
  a5 : getr regs a5 = w 1
  ra : getr regs ra = w 0x10012b8

/-- `next`: `off = off + 2 + len`.  `IH` is the walk from any later offset. -/
theorem next_block {size m : Nat} (Hsize : size < 250) (Hm : model_ok model)
    (IH : ∀ (regs : BvMap word) (off : Nat), size - off ≤ m → off + 2 ≤ size →
      tgt_regs regs size → getr regs t0 = w off →
      PM cfg (mkst regs (BitVec.ofInt 64 0x10011bc) mem rom) model)
    {off len : Nat} (H : tgt_regs regs size)
    (ha7 : getr regs a7 = w (off + 2)) (ha6 : getr regs a6 = w len)
    (hle : off + 2 + len ≤ size) (hm : size - (off + 2 + len) ≤ m) :
    PM cfg (mkst regs (BitVec.ofInt 64 0x10011b0) mem rom) model := by
  obtain ⟨h0, h1, h3, h4, h5, hra⟩ := H
  wst step_add, F_10011b0, D_010882b3
  wst step_sub, F_10011b4, D_40558833
  by_cases hr : 1 < size - (off + 2 + len)
  · wbr step_bgeu_ft, F_10011b8, D_0507f663
    exact IH _ (off + 2 + len) hm (by omega) (by constructor <;> wnv) (by wnv)
  · wbr step_bgeu_tk, F_10011b8, D_0507f663
    exact done_block Hm (by wnv)

/-- `sum_loop`: the cursor walks up to `stop`, every read inside the buffer. -/
theorem sum_loop {size off len stop : Nat} (Hm : model_ok model)
    (Hnext : ∀ regs : BvMap word, tgt_regs regs size →
      getr regs a7 = w (off + 2) → getr regs a6 = w len →
      PM cfg (mkst regs (BitVec.ofInt 64 0x10011b0) mem rom) model)
    (hstop : stop ≤ input_base + BUF) :
    ∀ (fuel : Nat) (regs : BvMap word) (cur : Nat), stop - cur ≤ fuel →
      input_base ≤ cur → cur < stop → tgt_regs regs size →
      getr regs a7 = w (off + 2) → getr regs a6 = w len →
      getr regs t0 = w stop → getr regs t1 = w cur →
      PM cfg (mkst regs (BitVec.ofInt 64 0x10011e0) mem rom) model := by
  intro fuel
  induction fuel with
  | zero => intro regs cur hf _ hc; omega
  | succ fuel ih =>
    intro regs cur hf hlo hc H ha7 ha6 ht0 ht1
    obtain ⟨h0, h1, h3, h4, h5, hra⟩ := H
    obtain ⟨b, hb⟩ := rdn_buf mem cur hlo (by omega)
    wlbu b, F_10011e0, D_00034383
    wst step_addi, F_10011e4, D_00130313
    wst step_addw, F_10011e8, D_0076063b
    by_cases hd : cur + 1 = stop
    · wbr step_bne_ft, F_10011ec, D_fe531ae3
      wrule (step_jal_x0 (Hfetch := F_10011f0) (Hecall := rfl) (Hdecode := D_fc1ff06f) ..)
      exact Hnext _ (by constructor <;> wnv) (by wnv) (by wnv)
    · wbr step_bne_tk, F_10011ec, D_fe531ae3
      exact ih _ (cur + 1) (by omega) (by omega) (by omega)
        (by constructor <;> wnv) (by wnv) (by wnv) (by wnv) (by wnv)

/-- `head`: one record.  The measure is the data left to walk. -/
theorem head {size : Nat} (Hsize : size < 250) (Hm : model_ok model) :
    ∀ (m : Nat) (regs : BvMap word) (off : Nat), size - off ≤ m → off + 2 ≤ size →
      tgt_regs regs size → getr regs t0 = w off →
      PM cfg (mkst regs (BitVec.ofInt 64 0x10011bc) mem rom) model := by
  intro m
  induction m with
  | zero => intro regs off hm ho; omega
  | succ m ih =>
    intro regs off hm ho H ht0
    obtain ⟨h0, h1, h3, h4, h5, hra⟩ := H
    wst step_add, F_10011bc, D_00568833
    obtain ⟨b, hb⟩ := rdn_buf mem (0x1003f07 + off) (by omega) (by omega)
    have hbl : b.toNat < 256 := b.isLt
    wlbu b, F_10011c0, D_00084803
    wst step_addi, F_10011c4, D_00228893
    wst step_sub, F_10011c8, D_41158333
    by_cases hbad : size - (off + 2) < b.toNat
    · -- the record runs past the data: `return -1`
      wbr step_bltu_tk, F_10011cc, D_03036863
      wst step_addi, F_10011fc, D_fff00513
      exact me_ret Hm (by wnv) F_1001200
    · wbr step_bltu_ft, F_10011cc, D_03036863
      by_cases hz : b.toNat = 0
      · wbr step_beq_tk, F_10011d0, D_fe0800e3
        exact next_block Hsize Hm ih (off := off) (len := b.toNat)
          (by constructor <;> wnv) (by wnv) (by wnv) (by omega) (by omega)
      · wbr step_beq_ft, F_10011d0, D_fe0800e3
        wst step_add, F_10011d4, D_01150333
        wst step_add, F_10011d8, D_010282b3
        wst step_add, F_10011dc, D_005702b3
        exact sum_loop (off := off) (len := b.toNat) (stop := 0x1003f08 + (off + b.toNat)) Hm
          (fun _ H' h7 h6 => next_block Hsize Hm ih H' h7 h6 (by omega) (by omega)) (by omega)
          _ _ (0x1003f06 + (off + 2)) (Nat.le_refl _) (by omega) (by omega)
          (by constructor <;> wnv) (by wnv) (by wnv) (by wnv) (by wnv)

/-- The target's entry, with `data` and `size` as the driver passes them. -/
theorem target_entry {size : Nat} (Hsize : size < 250) (Hm : model_ok model)
    (h0 : getr regs a0 = w 0x1003f06) (h1 : getr regs a1 = w size)
    (hra : getr regs ra = w 0x10012b8) :
    PM cfg (mkst regs (BitVec.ofInt 64 0x1001190) mem rom) model := by
  wst step_addi, F_1001190, D_00200613
  by_cases hs : size < 2
  · wbr step_bltu_tk, F_1001194, D_06c5e063
    wst step_addi, F_10011f4, D_00000513
    exact me_ret Hm (by wnv) F_10011f8
  · wbr step_bltu_ft, F_1001194, D_06c5e063
    wst step_addi, F_1001198, D_00000613
    wst step_addi, F_100119c, D_00000293
    wst step_addi, F_10011a0, D_00150693
    wst step_addi, F_10011a4, D_00250713
    wst step_addi, F_10011a8, D_00100793
    wrule (step_jal_x0 (Hfetch := F_10011ac) (Hecall := rfl) (Hdecode := D_0100006f) ..)
    exact head Hsize Hm _ _ 0 (Nat.le_refl _) (by omega) (by constructor <;> wnv) (by wnv)

/- =========================================================================
   The driver
   ========================================================================= -/

/-- `exit(2)`, at each of the driver's refusal sites. -/
theorem me_exit2 {pc1 pc2 pc3 pc4 pc5 : word} (Hm : model_ok model)
    (F1 : fetch_word plain_segs pc1 = some 0x05e00893)
    (F2 : fetch_word plain_segs pc2 = some 0x00200513)
    (F3 : fetch_word plain_segs pc3 = some 0x00000593)
    (F4 : fetch_word plain_segs pc4 = some 0x00000613)
    (F5 : fetch_word plain_segs pc5 = some 0x00000073)
    (h2 : v_addi pc1 4 = pc2) (h3 : v_addi pc2 4 = pc3)
    (h4 : v_addi pc3 4 = pc4) (h5 : v_addi pc4 4 = pc5) :
    PM cfg (mkst regs pc1 mem rom) model := by
  subst h2 h3 h4 h5
  wst step_addi, F1, D_05e00893
  wst step_addi, F2, D_00200513
  wst step_addi, F3, D_00000593
  wst step_addi, F4, D_00000613
  wecall F5
  exact me_exit (n := 2) Hm (by wnv) (by wnv) (by decide)

/-- `eof`: refuse a short input, otherwise call the target. -/
theorem eof_block {n : Nat} (Hn : n < BUF) (Hm : model_ok model)
    (h3 : getr regs a3 = w n) (h4 : getr regs a4 = w 0x1003000) :
    PM cfg (mkst regs (BitVec.ofInt 64 0x1001288) mem rom) model := by
  wst step_addi, F_1001288, D_00500513
  by_cases hs : 5 < n
  · wbr step_bltu_tk, F_100128c, D_00d56c63
    -- `size = n - 6`, the one subtraction the FIXED check makes safe
    have hsz : v_addi (w n) (0xffa#12 : BitVec 12).toInt = w (n - 6) := by
      apply BitVec.eq_of_toNat_eq
      have hi : (0xffa#12 : BitVec 12).toInt = -6 := by decide
      simp only [v_addi, hi, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    wst step_addi, F_10012a4, D_ffa68593
    wst step_addi, F_10012a8, D_7ff70513
    wst step_addi, F_10012ac, D_70750513
    wst step_auipc, F_10012b0, D_00000097
    wst step_jalr_gen, F_10012b4, D_ee0080e7
    exact target_entry (size := n - 6) (by omega) Hm (by wnv) (by wnv) (by wnv; rfl)
  · wbr step_bltu_ft, F_100128c, D_00d56c63
    exact me_exit2 Hm F_1001290 F_1001294 F_1001298 F_100129c F_10012a0 rfl rfl rfl rfl

/-- `read_loop`.  The measure is the room left in the buffer. -/
theorem read_loop :
    ∀ (fuel : Nat) (regs : BvMap word) (mem : word → Option byte) (model : Model) (n : Nat),
      BUF - n ≤ fuel → n < BUF → model_ok model →
      getr regs a3 = w n → getr regs a4 = w 0x1003000 → getr regs a5 = w BUF →
      getr regs a7 = w 63 →
      PM cfg (mkst regs (BitVec.ofInt 64 0x1001238) mem rom) model := by
  intro fuel
  induction fuel with
  | zero => intro regs mem model n hf hn; omega
  | succ fuel ih =>
    intro regs mem model n hf hn Hm h3 h4 h5 h7
    wst step_add, F_1001238, D_00d70533
    wst step_sub, F_100123c, D_40d78633
    wst step_addi, F_1001240, D_7ff50513
    wst step_addi, F_1001244, D_70150593
    wst step_addi, F_1001248, D_00000513
    wecall F_100124c
    refine me_read (buf := input_base + n) (cnt := BUF - n) Hm
      ⟨by wnv, by wnv, ?_, by wnv, by omega, by omega,
        wseg_ok_drop _ n _ _ (by rw [show n + (BUF - n) = BUF by omega]; exact input_writable)⟩
      ?_ ?_
    · wnv
      congr 1
      omega
    · -- end of input
      wbr step_blt_ft, F_1001250, D_02054263
      wbr step_beq_tk, F_1001254, D_02050a63
      exact eof_block hn Hm (by wnv) (by wnv)
    · -- a block of `bs.length` bytes
      intro bs hlo hhi
      have Hm' := model_ok_take bs.length Hm
      wbr step_blt_ft, F_1001250, D_02054263
      wbr step_beq_ft, F_1001254, D_02050a63
      wst step_add, F_1001258, D_00d506b3
      by_cases hfull : bs.length + n = BUF
      · wbr step_bne_ft, F_100125c, D_fcf69ee3
        exact me_exit2 Hm' F_1001260 F_1001264 F_1001268 F_100126c F_1001270 rfl rfl rfl rfl
      · wbr step_bne_tk, F_100125c, D_fcf69ee3
        exact ih _ _ _ (bs.length + n) (by omega) (by omega) Hm' (by wnv) (by wnv) (by wnv) (by wnv)

/-- `_start`, from the state `execve` leaves. -/
theorem start {sp0 : word} (Hm : model_ok model) (hsp : getr regs sp = sp0)
    (hstore : store_ok plain_segs mem (v_addi (v_addi sp0 (-16)) 8) 8 = true) :
    PM cfg (mkst regs (BitVec.ofInt 64 0x100121c) mem rom) model := by
  have hi : (0xff0#12 : BitVec 12).toInt = -16 := by decide
  have ha8 : (0x008#12 : BitVec 12).toInt = 8 := by decide
  have hlui : v_lui (zshiftl (0x01003#20 : BitVec 20).toInt 12) = w 0x1003000 := by decide
  wst step_addi, F_100121c, D_ff010113
  wrule (step_sd_val (Hfetch := F_1001220) (Hecall := rfl) (Hdecode := D_00113423)
    (Hok := by wnv) ..)
  wst step_addi, F_1001224, D_00000693
  wst step_lui, F_1001228, D_01003737
  wst step_addi, F_100122c, D_00070713
  wst step_addi, F_1001230, D_10000793
  wst step_addi, F_1001234, D_03f00893
  exact read_loop _ _ _ _ 0 (Nat.le_refl _) (by omega) Hm (by wnv) (by wnv) (by wnv) (by wnv)

/- =========================================================================
   The statements
   ========================================================================= -/

/-- One proof, at every environment configuration. -/
theorem plain_must_exit (cfg : SpuriousCfg) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (Hen : valid_entry plain en inp) (Hinp : valid_input inp) :
    must_exit_in_scfg cfg ok_or_refused plain lim en inp := by
  obtain ⟨hlo, hhi⟩ := entry_sp_window plain en inp Hen Hinp
  obtain ⟨sp0, brk0, mbase, rnd⟩ := en
  show must_exit_in_at_cfg cfg plain_segs ok_or_refused
    ⟨init_machine_state plain_segs plain_mem.init_pc plain_mem.phdrs sp0 rnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap,
     init_model (segments_reserved plain_segs) brk0 mbase sp0 lim inp⟩
  rw [init_mkst]
  exact start (model_ok_init _ _ _ _ _ _) (getr_regupd_same _ _ _ (by decide))
    (frame_store_ok _ _ _ _ _ _ _ _ hlo hhi)

theorem plain_halts_holds : Statements.halts plain :=
  fun en inp Hen Hinp _ => plain_must_exit forced_only_cfg _ en inp Hen Hinp

theorem plain_halts_may_fail_holds : Statements.halts_may_fail plain :=
  fun en inp Hen Hinp => plain_must_exit may_fail_cfg _ en inp Hen Hinp

end LinuxSem.Examples.FuzzTlv.FixedProof
