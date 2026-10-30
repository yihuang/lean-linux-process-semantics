/-
  * Common.LibWritev — `writev` to a channel fd with SHORT WRITES, as a shape node.

  Image-independent (Section over `segs`).

  musl's `__stdio_write` flushes a FILE with

      writev(f->fd, iov, iovcnt)     iov = [{f->wbase, f->wpos - f->wbase}, {buf, len}]

  where (musl 1.2.6) an EMPTY first iovec is dropped before the first call
  (`iovcnt = 1`, `iov = &iovs[1]`), and the retry loop re-issues the call on
  the undelivered remainder.

  THE SPEC (`ReadWrite.writev_spec`): on a channel fd the kernel delivers a
  NONDETERMINISTIC NONEMPTY PREFIX of the gathered bytes `bs = bs1 ++ bs2` —
  any `k` with `1 <= k <= length bs` — emitting `map (WriteEv fd) (firstn k bs)`
  and returning `k`; memory and model are unchanged.  The vector must be fully
  readable (iovec array and both buffers: then the gatherable prefix is the
  whole flattening) AND inside the user address space (`access_okb`, i.e.
  `base + len <= TASK_SIZE` for the array and for every buffer — the import
  path tests each range before it reads it), its total must be `>= 1` (a zero
  total is the degenerate `ret_only 0`, see `rz_writev1_zero`),
  `<= rw_bytes_max` (else UNMODELED — kept symbolic) and `<= 2^30` (below the
  kernel's `MAX_RW_COUNT` clamp and the error-encoding range).

  Provided:
  - `writev_check`        : the checker's exact answer family at the ecall;
  - `rz_writev_pending`   : the node at the pending state, continuation
                            quantified over the delivered length `k` AND
                            allowed to depend on it (shape `t_alt (fun i :
                            wr_index bs => t_emit (map (WriteEv fd) (firstn i
                            bs)) (T i))`);
  - `rz_writev2` / `rz_writev1` : the `mkst`/`getr` forms for iovcnt 2 / 1;
  - `rz_writev2_wall` / `rz_writev1_wall` : the packaged form the
    `__stdio_write` LOOP proof uses: if after every delivery `k` the rest of
    the loop realizes `t_emit (map (WriteEv fd) (skipn k bs)) K`, the call site
    realizes `t_emit (map (WriteEv fd) bs) K` — short writes are invisible in
    the trace (`ShapeAlg.t_alt_wall`);
  - `rz_writev2_ch` : the full-delivery special case as a plain continuation
    (`t_write_ch`);
  - `rz_writev1_zero` : the degenerate zero-total call (ret 0, no event);
  - `t_alt_wall_nat` : the same trace identity indexed by a bare `nat` range
    instead of `wr_index`.

  NOTES
  ==========

  (1) NAMES.  `Z` is `Int`, `N`/`nat` are
      `Nat`, `word` is `BitVec 64` and `byte` is `BitVec 8`.
  (2) STILL DEFERRED.  Only `rz_writev1_zero`, the degenerate zero-total
      `writev(fd, [{b1, 0}], 1)`.  Its exact statement is at the end of this
      file.  It needs no new idea, only the single-descriptor import reduction
      (`import_iovecs`'s `nr_segs == 1` short circuit at a zero-length
      descriptor) and the `check_ret_only_copyins` inversion.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Common.SharedFacts
import LinuxSem.Common.AgentNodes

set_option autoImplicit false

namespace LinuxSem.Common.LibWritev

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.LinuxProcessSem.Sys.Syscall (fd32 fd32_id w_is0 w_is0_pos)
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite (iovcnt32)
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Fs.ReadWrite (check_writev)

/-  ambient `FPState` instance (`Local Instance libwritev_fx`):
   `PropExec.mkst`'s FP half is a typeclass field, and `LibWritev` pins
   it to the process-entry one, so the `PropExec` step lemmas and this
   file's `mkst` states are stated at the same shape. -/
local instance libwritev_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

open LinuxSem.Common.PropExec (mkst getr regupd v_addi step_ecall le_word_v
  arg_reg_0 arg_reg_1 arg_reg_2 getr_nz u64_range seg_rom rdn rdn_length)
open LinuxSem.Common.SeqExec (bytes_le_to_Z_8)
open LinuxSem.Common.CatSim (read_bytes_map_read_byte apply_effect_no_write
  apply_effect_copyins_no_write)
open LinuxSem.Common.CatExec (ms_read_bytes_aux_rdn ms_read_bytes_rdn)
open LinuxSem.Common.ExitSim (sstep_instr_inv)
open LinuxSem.Common.ShapeAlg (is_prefix_app_split is_prefix_nil_r TSet t_eq t_eq_refl
  t_eq_sym t_eq_trans t_nil t_emit t_alt t_alt2 wr_index wr_full t_write_ch t_emit_nil_eq
  t_alt_wall node_ok realizes realizes_nonempty mkCfg node_instr rz_silent1 rz_step)
open LinuxSem.Common.Nodes (halt_ev sstep_of_check sstep_svc_inv)
open LinuxSem.Common.FileSim (in_sysno_si in_mem_si in_arg0_si in_arg1_si in_arg2_si)
open LinuxSem.Common.AgentNodes (epend step_ecall_epend epend_svc ms_gpr_epend0 ms_gpr_epend1
  ms_gpr_epend2 ms_mem_epend ms_rom_epend adv_set_epend rz_sys)
open LinuxSem.LinuxProcessSem.Sys.Uapi (mod_mul_256_of mod_mul_256)
open LinuxSem.Common.SharedFacts

/-! =========================================================================
    LibWritev — image-independent prelude
    ========================================================================= -/

/-- `a + b` in `Int` form: the `bv` addition is the `Int` addition of the
    unsigned values, truncated to 64 bits by `Z_to_bv`. -/
theorem bv_add_Zform (a b : word) :
    a + b = BitVec.ofInt 64 ((a.toNat : Int) + (b.toNat : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  have h : ((a.toNat : Int) + (b.toNat : Int)) = ((a.toNat + b.toNat : Nat) : Int) := by
    omega
  rw [h]
  rfl

/-- `word_to_nat` of a small literal word is the literal. -/
theorem word_to_nat_Z (z : Int) (Hz1 : 0 ≤ z) (Hz2 : z < 2 ^ 64) :
    word_to_nat (BitVec.ofInt 64 z) = z.toNat := by
  unfold word_to_nat
  rw [BitVec.toNat_ofInt]
  have h2' : z < ((2 ^ 64 : Nat) : Int) := by
    rw [← show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from by decide]
    exact Hz2
  rw [Int.emod_eq_of_lt Hz1 h2']

theorem u64_roundtrip' (x : word) :
    BitVec.ofInt 64 (x.toNat : Int) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have h2' : (x.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by
    have := x.isLt
    rw [← show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from by decide]
    omega
  rw [Int.emod_eq_of_lt (by omega) h2']
  rfl

/-- `access_okb` from the one inequality the caller has
    (`Uaccess.access_okb_intro` takes the length as a word; the import path
    also asks it of `Int` lengths). -/
theorem access_okb_of_le (b : word) (n : Int)
    (_Hn : 0 ≤ n) (H : (b.toNat : Int) + n ≤ TASK_SIZE) :
    access_okb b n = true := by
  unfold access_okb
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor <;> omega

/-- `u64_lit`: a small literal's unsigned value is the literal. -/
theorem u64_lit (z : Int) (h1 : 0 ≤ z) (h2 : z < 2 ^ 64) :
    (BitVec.ofInt 64 z).toNat = z.toNat := by
  rw [BitVec.toNat_ofInt]
  have h2' : z < ((2 ^ 64 : Nat) : Int) := by
    rw [← show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from by decide]
    exact h2
  rw [Int.emod_eq_of_lt h1 h2']

/-! =========================================================================
    The trace identity that makes short writes harmless
    ========================================================================= -/

/-- `ShapeAlg.t_alt_wall`, re-indexed by a plain `nat` with an explicit range
    guard (the spelling a loop proof by induction on the remainder finds
    convenient): choosing ANY nonempty delivered prefix and then emitting the
    rest is, as a trace set, emitting the whole buffer. -/
theorem t_alt_wall_nat (ch : word) (bs : List byte) (K : TSet)
    (HK : K []) (Hnb : 1 ≤ bs.length) :
    t_eq (t_alt (fun k : Nat =>
            fun tr => (1 ≤ k ∧ k ≤ bs.length) ∧
              t_emit ((bs.take k).map (event.WriteEv ch))
                     (t_emit ((bs.drop k).map (event.WriteEv ch)) K) tr))
         (t_emit (bs.map (event.WriteEv ch)) K) := by
  intro tr
  rw [← t_alt_wall ch bs K HK Hnb tr]
  unfold t_alt
  constructor
  · rintro ⟨k, Hk, Ht⟩
    exact ⟨⟨k, Hk⟩, Ht⟩
  · rintro ⟨⟨k, Hk⟩, Ht⟩
    exact ⟨k, Hk, Ht⟩

/-- The packaged consequence rule: a node delivering any nonempty prefix,
    each continuation emitting the corresponding remainder, realizes the full
    emission. -/
theorem rz_wall (segs : List Segment) (c : config) (ch : word) (bs : List byte)
    (K : TSet) (Hnb : 1 ≤ bs.length) (HK : K [])
    (H : realizes segs c (t_alt (fun i : wr_index bs =>
      t_emit ((bs.take i.1).map (event.WriteEv ch))
             (t_emit ((bs.drop i.1).map (event.WriteEv ch)) K)))) :
    realizes segs c (t_emit (bs.map (event.WriteEv ch)) K) :=
  realizes.rz_conseq c _ _ H (t_alt_wall ch bs K HK Hnb)

/-! =========================================================================
    The iovec layer (`Section WithSegs`)
    ========================================================================= -/

section WithSegs

variable (segs : List Segment)

/-- Read an 8-byte word through `rdn` and decode it. -/
theorem read_u64_rdn (ms : machine_state) (a v : word)
    (Hrom : ms.ms_rom = seg_rom segs)
    (H : rdn segs ms.ms_mem a 8 = some (word_to_le_bytes 8 v)) :
    read_u64 (ms_read_byte ms) a = some v := by
  unfold read_u64
  rw [read_bytes_map_read_byte, ms_read_bytes_rdn segs ms a (BitVec.ofInt 64 8) Hrom]
  have h8 : word_to_nat (BitVec.ofInt 64 8) = 8 := by decide
  rw [h8, H]
  simp only [Option.some.injEq]
  exact le_word_v _ _ (bytes_le_to_Z_8 v)

theorem read_bytes_map_rdn (ms : machine_state) (a n : word) (bs : List byte)
    (Hrom : ms.ms_rom = seg_rom segs)
    (H : rdn segs ms.ms_mem a (word_to_nat n) = some bs) :
    read_bytes_map (ms_read_byte ms) a n = some bs := by
  rw [read_bytes_map_read_byte, ms_read_bytes_rdn segs ms a n Hrom]
  exact H

/-- The iovec array at `iov` decodes to `iovs` (each entry: base, then length,
    8-byte little-endian; lengths below 2^63). -/
def iov_array (mem : word → Option byte) (iov : word) (iovs : List (word × word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8 = some (word_to_le_bytes 8 b) ∧
      rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8 = some (word_to_le_bytes 8 n) ∧
      (n.toNat : Int) < 2 ^ 63 ∧
      iov_array mem (BitVec.ofInt 64 ((iov.toNat : Int) + 16)) r

theorem read_iovec_entry_of_array (ms : machine_state) (b n : word)
    (r : List (word × word)) (iov : word)
    (Hrom : ms.ms_rom = seg_rom segs)
    (Ha : iov_array segs ms.ms_mem iov ((b, n) :: r)) :
    read_iovec_entry (ms_read_byte ms) iov = .IovEntry b n := by
  obtain ⟨Hb, Hn, Hlt, _⟩ := Ha
  unfold read_iovec_entry
  rw [read_u64_rdn segs ms iov b Hrom Hb]
  rw [show iov + (8 : word) = BitVec.ofInt 64 ((iov.toNat : Int) + 8)
      from bv_add_Zform iov 8]
  rw [read_u64_rdn segs ms _ n Hrom Hn]
  dsimp only
  have hgt : ¬ (2 ^ 63 : Int) ≤ (n.toNat : Int) := by omega
  rw [ite_eq_right hgt]

theorem copy_iovecs_of_array (ms : machine_state) (iovs : List (word × word)) :
    ∀ (iov : word), ms.ms_rom = seg_rom segs →
      iov_array segs ms.ms_mem iov iovs →
      copy_iovecs_aux (ms_read_byte ms) iov iovs.length = .ImpOk iovs := by
  induction iovs with
  | nil => intro iov _ _; rfl
  | cons hd rest ih =>
    obtain ⟨b, n⟩ := hd
    intro iov Hrom Ha
    simp only [List.length_cons, copy_iovecs_aux]
    rw [read_iovec_entry_of_array segs ms b n rest iov Hrom Ha]
    obtain ⟨_, _, _, Hr⟩ := Ha
    rw [show iov + (16 : word) = BitVec.ofInt 64 ((iov.toNat : Int) + 16)
        from bv_add_Zform iov 16]
    rw [ih _ Hrom Hr]

/-- The source buffers: every entry's `len` bytes at `base` are readable. -/
def iov_bufs (mem : word → Option byte) (iovs : List (word × word))
    (bss : List (List byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = some bs ∧ iov_bufs mem r bss'
  | _, _ => False

theorem gather_of_bufs (ms : machine_state) (iovs : List (word × word)) :
    ∀ (bss : List (List byte)), ms.ms_rom = seg_rom segs →
      iov_bufs segs ms.ms_mem iovs bss →
      gather_iovecs (ms_read_byte ms) iovs = some bss.flatten := by
  induction iovs with
  | nil =>
    intro bss Hrom Hb
    cases bss with
    | nil => rfl
    | cons _ _ => exact False.elim Hb
  | cons hd rest ih =>
    obtain ⟨b, n⟩ := hd
    intro bss Hrom Hb
    cases bss with
    | nil => exact False.elim Hb
    | cons bs bss' =>
      obtain ⟨H1, H2⟩ := Hb
      simp only [gather_iovecs, List.flatten_cons]
      rw [read_bytes_map_rdn segs ms b n bs Hrom H1, ih bss' Hrom H2]

theorem cap_iovecs_id (iovs : List (word × word)) :
    ∀ (left : Int), iovs_total iovs ≤ left → cap_iovecs_aux iovs left = iovs := by
  induction iovs with
  | nil => intro left _; rfl
  | cons hd rest ih =>
    obtain ⟨b, n⟩ := hd
    intro left H
    simp only [cap_iovecs_aux, iovs_total] at *
    have hnn := iovs_total_nonneg rest
    have hmin : min left (n.toNat : Int) = (n.toNat : Int) := by omega
    rw [hmin]
    rw [show (BitVec.ofInt 64 (n.toNat : Int)) = n from u64_roundtrip' n]
    rw [ih _ (by omega)]

/-- Every buffer lies inside the user address space — what the import path's
    per-segment `access_okb` asks (`base + len <= TASK_SIZE`). -/
def iov_bufs_ok (iovs : List (word × word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => (b.toNat : Int) + (n.toNat : Int) ≤ TASK_SIZE ∧ iov_bufs_ok r

theorem iovs_access_okb_of_ok (iovs : List (word × word))
    (H : iov_bufs_ok iovs) : iovs_access_okb iovs = true := by
  induction iovs with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨b, n⟩ := hd
    obtain ⟨Hb, Hr⟩ := H
    simp only [iovs_access_okb, List.all_cons, Bool.and_eq_true]
    exact ⟨access_okb_intro b n Hb, ih Hr⟩

/-- The import path (`State.import_iovecs`): a readable, in-range vector of
    `1..1024` entries imports as itself. -/
theorem import_iovecs_of_array (ms : machine_state) (iovs : List (word × word))
    (iov : word) (Hrom : ms.ms_rom = seg_rom segs)
    (Hcnt : 1 ≤ iovs.length ∧ iovs.length ≤ 1024)
    (Hiok : (iov.toNat : Int) + 16 * (iovs.length : Int) ≤ TASK_SIZE)
    (Harr : iov_array segs ms.ms_mem iov iovs)
    (Hbok : iov_bufs_ok iovs) :
    import_iovecs (ms_read_byte ms) iov (BitVec.ofInt 64 (iovs.length : Int)) = .ImpOk iovs := by
  obtain ⟨Hc1, Hc2⟩ := Hcnt
  cases iovs with
  | nil => simp at Hc1
  | cons hd rest =>
    obtain ⟨b, n⟩ := hd
    cases rest with
    | nil =>
      -- ONE entry: `__import_iovec`'s `nr_segs == 1` short-circuit
      obtain ⟨Hb, Hn, Hlt, _⟩ := Harr
      obtain ⟨Hokb, _⟩ := Hbok
      simp only [List.length_cons, List.length_nil] at Hc1 Hc2 Hiok ⊢
      unfold import_iovecs
      have h1 : bv_eqb (BitVec.ofInt 64 ((1 : Nat) : Int)) (1 : word) = true := by
        rw [bv_eqb_eq]
        rfl
      rw [ite_eq_left h1]
      have hok16 : access_okb iov 16 = true :=
        access_okb_of_le iov 16 (by omega) (by omega)
      rw [hok16]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      rw [read_iovec_entry_of_array segs ms b n [] iov Hrom ⟨Hb, Hn, Hlt, trivial⟩]
      dsimp only
      have hMAX : (0 : Int) ≤ MAX_RW_COUNT := by unfold MAX_RW_COUNT; decide
      have hokn : access_okb b (min (n.toNat : Int) MAX_RW_COUNT) = true :=
        access_okb_of_le b _
          (by have := Int.min_le_left (n.toNat : Int) MAX_RW_COUNT; omega)
          (by have hle := Int.min_le_left (n.toNat : Int) MAX_RW_COUNT; omega)
      rw [hokn]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    | cons hd2 rest2 =>
      -- TWO or more: the general `copy_iovecs_aux` + `access_ok` path
      obtain ⟨b2, n2⟩ := hd2
      obtain ⟨Hb, Hn, Hlt, Harr'⟩ := Harr
      obtain ⟨Hbok, Hbok'⟩ := Hbok
      generalize hL : ((b, n) :: (b2, n2) :: rest2).length = L at Hc1 Hc2 Hiok ⊢
      have hL2 : 2 ≤ L := by rw [← hL]; simp
      have hL1024 : L ≤ 1024 := Hc2
      have hL64 : ((L : Int)) < 2 ^ 64 := by
        have : ((1024 : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by decide
        omega
      have hval : (BitVec.ofInt 64 ((L : Int))).toNat = L := by
        rw [u64_lit]
        · omega
        · omega
        · omega
      have hne1 : bv_eqb (BitVec.ofInt 64 ((L : Int))) (1 : word) = false := by
        have h : ¬ (BitVec.ofInt 64 (L : Int)) = (1 : word) := by
          intro heq
          have h3 := congrArg BitVec.toNat heq
          rw [hval] at h3
          simp at h3
          omega
        simpa [bv_eqb] using h
      have hne0 : bv_eqb (BitVec.ofInt 64 ((L : Int))) (0 : word) = false := by
        have h : ¬ (BitVec.ofInt 64 (L : Int)) = (0 : word) := by
          intro heq
          have h3 := congrArg BitVec.toNat heq
          rw [hval] at h3
          simp at h3
          omega
        simpa [bv_eqb] using h
      have hvalZ : (((BitVec.ofInt 64 ((L : Int))).toNat : Nat) : Int) = (L : Int) := by
        rw [hval]
      have hIOV : ¬ IOV_MAX < (((BitVec.ofInt 64 ((L : Int))).toNat : Nat) : Int) := by
        rw [hvalZ]
        show ¬ (1024 : Int) < (L : Int)
        omega
      have hok16 : access_okb iov (16 * (((BitVec.ofInt 64 ((L : Int))).toNat : Nat) : Int)) = true := by
        rw [hvalZ]
        apply access_okb_of_le
        · omega
        · exact Hiok
      have hcopy : copy_iovecs_aux (ms_read_byte ms) iov
            (word_to_nat (BitVec.ofInt 64 ((L : Int))))
          = .ImpOk ((b, n) :: (b2, n2) :: rest2) := by
        rw [show word_to_nat (BitVec.ofInt 64 ((L : Int))) = L from by
          unfold word_to_nat
          rw [hval]]
        rw [← hL]
        exact copy_iovecs_of_array segs ms ((b, n) :: (b2, n2) :: rest2) iov Hrom
          ⟨Hb, Hn, Hlt, Harr'⟩
      have hacc : iovs_access_okb ((b, n) :: (b2, n2) :: rest2) = true :=
        iovs_access_okb_of_ok _ ⟨Hbok, Hbok'⟩
      unfold import_iovecs
      have hg1 : ¬ (bv_eqb (BitVec.ofInt 64 ((L : Int))) (1 : word) = true) := by
        rw [hne1]; simp
      have hg0 : ¬ (bv_eqb (BitVec.ofInt 64 ((L : Int))) (0 : word) = true) := by
        rw [hne0]; simp
      rw [ite_eq_right hg1, ite_eq_right hg0, ite_eq_right hIOV]
      simp only [hok16, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hcopy]
      dsimp only
      rw [hacc]
      simp only [ite_true]

end WithSegs

/-! =========================================================================
    `check_syscall` at sysno 66 is `check_writev`
    ========================================================================= -/

/-- The `DispatchCompute` lemma restated here (same proof), so this file does
    not import the dispatch tree and its `Progress` closure (a closure guard;
    the `RefNodes` idiom). -/
theorem check_syscall_writev (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : i.in_sysno.toNat = 66) :
    check_syscall i eff m
      = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have h : LinuxSem.Checks.Sys.Dispatch.lookup_ca
      LinuxSem.Checks.Sys.Dispatch.checked_table (i.in_sysno.toNat : Int)
      = some LinuxSem.Checks.Sys.Dispatch.arm_writev := by
    rw [H]
    arm_dispatch
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, h,
    LinuxSem.Checks.Sys.Dispatch.ca_check_arm_writev]

/-! =========================================================================
    The checker at a writev ecall
    ========================================================================= -/

section WithSegsChecker

variable (segs : List Segment)

/-- The checker at a writev ecall on channel `fd` with a fully readable,
    in-range vector of total `tot` in `[1, min rw_bytes_max 2^30]`: the
    admissible answers are exactly the nonempty delivered prefixes. -/
theorem writev_check (ms : machine_state) (x8 : word) (model : Model)
    (fd : Int) (iov : word) (iovs : List (word × word)) (bss : List (List byte))
    (Hrom : ms.ms_rom = seg_rom segs)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (Hno : x8.toNat = 66)
    (H0 : ms_gpr ms 0 = BitVec.ofInt 64 fd)
    (H1 : ms_gpr ms 1 = iov)
    (H2 : ms_gpr ms 2 = BitVec.ofInt 64 (iovs.length : Int))
    (Hcnt : 1 ≤ iovs.length ∧ iovs.length ≤ 1024)
    (Hiok : (iov.toNat : Int) + 16 * (iovs.length : Int) ≤ TASK_SIZE)
    (Harr : iov_array segs ms.ms_mem iov iovs)
    (Hbok : iov_bufs_ok iovs)
    (Hbufs : iov_bufs segs ms.ms_mem iovs bss)
    (Ht1 : 1 ≤ iovs_total iovs) (_Htmax : iovs_total iovs ≤ rw_bytes_max)
    (Ht30 : iovs_total iovs ≤ 2 ^ 30) :
    (bss.flatten.length : Int) = iovs_total iovs ∧
    ∀ eff, check_syscall (sys_input segs ms x8) eff model
      = match eff with
        | .mkEffectU ret [] [] [] [] ci =>
            if decide (1 ≤ (ret.toNat : Int))
               && decide ((ret.toNat : Int) ≤ iovs_total iovs)
               && !(addr_is_error_b ret) then
              if access_ranges_eqb ci
                   (import_iovecs_accesses (ms_read_byte ms) iov
                      (BitVec.ofInt 64 (iovs.length : Int))
                    ++ iov_prefix_accesses iovs ret.toNat)
              then .CheckOk model ((bss.flatten.take ret.toNat).map (.WriteEv (BitVec.ofInt 64 fd)))
              else .CheckReject
            else .CheckReject
        | _ => .CheckReject := by
  have Hg : gather_iovecs (ms_read_byte ms) iovs = some bss.flatten :=
    gather_of_bufs segs ms iovs bss Hrom Hbufs
  have Hlen : ((bss.flatten.length : Nat) : Int) = iovs_total iovs :=
    gather_iovecs_length (ms_read_byte ms) iovs bss.flatten Hg
  have hlennat : bss.flatten.length ≤ 2 ^ 30 := by
    have := Hlen; omega
  -- the gates in front of the answer family
  have hbsne : bss.flatten.length ≠ 0 := by omega
  have htotne : iovs_total iovs ≠ 0 := by omega
  refine ⟨Hlen, ?_⟩
  intro eff
  rw [check_syscall_writev (sys_input segs ms x8) eff model (by rw [in_sysno_si]; exact Hno)]
  rw [in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2]
  -- the fd argument survives `fd32` (it is below 2^32)
  have hfdv : (BitVec.ofInt 64 fd).toNat = fd.toNat :=
    u64_lit fd (by omega) (by omega)
  have hfd32 : (BitVec.ofInt 64 fd).toNat < 2 ^ 32 := by rw [hfdv]; omega
  rw [fd32_id _ hfd32]
  -- the count argument survives `iovcnt32`
  have hcntv : (BitVec.ofInt 64 ((iovs.length : Nat) : Int)).toNat = iovs.length :=
    u64_lit _ (by omega) (by omega)
  have hcnt32 : iovcnt32 (BitVec.ofInt 64 ((iovs.length : Nat) : Int))
      = BitVec.ofInt 64 ((iovs.length : Nat) : Int) := by
    simp only [iovcnt32, LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32]
    apply BitVec.eq_of_toNat_eq
    rw [hcntv]
    show (BitVec.ofNat 64 (iovs.length % 2 ^ 32)).toNat = iovs.length
    rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  unfold check_writev
  rw [Hfd]
  dsimp only
  rw [show w_is0 (BitVec.ofInt 64 fd) = false from w_is0_pos _ (by rw [hfdv]; omega)]
  rw [in_mem_si]
  rw [hcnt32]
  rw [import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok]
  dsimp only
  -- the `cap_iovecs` clamp is the identity at this total
  have Hcap : cap_iovecs iovs = iovs := by
    unfold cap_iovecs
    exact cap_iovecs_id iovs MAX_RW_COUNT (by unfold MAX_RW_COUNT; omega)
  rw [Hcap]
  have hwg : writev_gathered (ms_read_byte ms) iovs = bss.flatten := by
    unfold writev_gathered
    rw [Hcap]
    exact gather_prefix_full (ms_read_byte ms) iovs bss.flatten Hg
  rw [hwg, Hlen]
  rw [show (iovs_total iovs == (0 : Int)) = false from beq_eq_false_iff_ne.mpr htotne,
      show (bss.flatten.length == 0) = false from beq_eq_false_iff_ne.mpr hbsne]
  simp only [Bool.false_eq_true, ite_false]
  have hlenv : (len_word bss.flatten).toNat = bss.flatten.length := by
    unfold len_word
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have herr : addr_is_error_b (len_word bss.flatten) = false := by
    unfold addr_is_error_b
    have h : ¬ (two_pow_64 - 4096 < ((len_word bss.flatten).toNat : Int)) := by
      rw [hlenv]; unfold two_pow_64; omega
    simp [h]
  rw [ite_eq_right (by rw [herr]; exact Bool.false_ne_true)]
  -- the answer family: only the no-write, no-copy effect reaches the gate
  cases eff with
  | mkEffectU ret ws zs us cs ci =>
    cases ws with
    | nil =>
      cases zs with
      | nil =>
        cases us with
        | nil =>
          cases cs with
          | nil => rfl
          | cons _ _ => rfl
        | cons _ _ => rfl
      | cons _ _ => rfl
    | cons _ _ => rfl

end WithSegsChecker

/-! =========================================================================
    The node at the pending state
    ========================================================================= -/

section WithSegsPending

variable (segs : List Segment)

/-- The node at the pending state: resolutions = delivered lengths. -/
theorem rz_writev_pending (ms : machine_state) (x8 : word) (model : Model)
    (fd : Int) (iov : word) (iovs : List (word × word)) (bss : List (List byte))
    (T : Nat → TSet)
    (Hrom : ms.ms_rom = seg_rom segs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31) (Hno : x8.toNat = 66)
    (H0 : ms_gpr ms 0 = BitVec.ofInt 64 fd) (H1 : ms_gpr ms 1 = iov)
    (H2 : ms_gpr ms 2 = BitVec.ofInt 64 (iovs.length : Int))
    (Hcnt : 1 ≤ iovs.length ∧ iovs.length ≤ 1024)
    (Hiok : (iov.toNat : Int) + 16 * (iovs.length : Int) ≤ TASK_SIZE)
    (Harr : iov_array segs ms.ms_mem iov iovs) (Hbok : iov_bufs_ok iovs)
    (Hbufs : iov_bufs segs ms.ms_mem iovs bss)
    (Ht1 : 1 ≤ iovs_total iovs) (Htmax : iovs_total iovs ≤ rw_bytes_max)
    (Ht30 : iovs_total iovs ≤ 2 ^ 30)
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ bss.flatten.length →
            realizes segs
              (mkCfg (advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 (k : Int)))) model)
              (T k)) :
    realizes segs (mkCfg ms model)
      (t_alt (fun i : wr_index bss.flatten =>
         t_emit ((bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) (T i.1))) := by
  obtain ⟨Hlen, Hchk⟩ :=
    writev_check segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok
      Harr Hbok Hbufs Ht1 Htmax Ht30
  have hnb : 1 ≤ bss.flatten.length := by omega
  -- one delivery: the effect the checker admits, and its successor
  let effs : wr_index bss.flatten → SyscallEffect := fun i =>
    ⟨BitVec.ofInt 64 (i.1 : Int), [], [], [], [],
      import_iovecs_accesses (ms_read_byte ms) iov (BitVec.ofInt 64 (iovs.length : Int))
        ++ iov_prefix_accesses iovs i.1⟩
  have hstep (i : wr_index bss.flatten) :
      check_syscall (sys_input segs ms x8) (effs i) model
        = .CheckOk model ((bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) := by
    have hk1 : 1 ≤ i.1 := i.2.1
    have hk2 : i.1 ≤ bss.flatten.length := i.2.2
    have hkv : (BitVec.ofInt 64 (i.1 : Int)).toNat = i.1 :=
      u64_lit _ (by omega) (by omega)
    have hi30 : ((i.1 : Nat) : Int) ≤ 2 ^ 30 := by
      have h1 : ((bss.flatten.length : Nat) : Int) ≤ 2 ^ 30 := by rw [Hlen]; exact Ht30
      omega
    have hle : ((i.1 : Nat) : Int) ≤ iovs_total iovs := by
      rw [← Hlen]; omega
    have herr : addr_is_error_b (BitVec.ofInt 64 (i.1 : Int)) = false := by
      unfold addr_is_error_b
      rw [hkv]
      exact decide_eq_false_iff_not.mpr (by unfold two_pow_64; omega)
    have h1 : decide (1 ≤ ((i.1 : Nat) : Int)) = true := by
      rw [decide_eq_true_eq]; omega
    have h2 : decide (((i.1 : Nat) : Int) ≤ iovs_total iovs) = true := by
      rw [decide_eq_true_eq]; exact hle
    have h3 : (!(addr_is_error_b (BitVec.ofInt 64 (i.1 : Int)))) = true := by
      rw [herr]; rfl
    have hcond : ((decide (1 ≤ ((i.1 : Nat) : Int))
        && decide (((i.1 : Nat) : Int) ≤ iovs_total iovs)
        && !(addr_is_error_b (BitVec.ofInt 64 (i.1 : Int)))) = true) := by
      rw [h1, h2, h3]; rfl
    rw [Hchk]
    dsimp only [effs]
    rw [hkv, ite_eq_left hcond, ite_eq_left (access_ranges_eqb_refl _)]
  refine realizes.rz_node (mkCfg ms model) (wr_index bss.flatten)
    (fun i =>
      (bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd)))
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 (i.1 : Int)))) model)
    (fun i => T i.1) (wr_full bss.flatten hnb) ?_ (fun i => Hk i.1 i.2.1 i.2.2)
  constructor
  · intro i
    have hgoal := sstep_of_check segs ms model x8 (effs i) model
      ((bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd)))
      Hh Hsvc (hstep i) Hh Hlazy
    rwa [show apply_effect ms (effs i)
          = set_gpr0 ms (BitVec.ofInt 64 (i.1 : Int)) from by
        dsimp only [effs]
        exact apply_effect_copyins_no_write ms _ _] at hgoal
  · intro e st hss
    have Hinv : ∀ (eff : SyscallEffect) (m' : Model) (ev : List event),
        check_syscall (sys_input segs ms x8) eff model = .CheckOk m' ev →
        ∃ i : wr_index bss.flatten,
          eff = effs i ∧ m' = model ∧
          ev = (bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd)) := by
      intro eff m' ev hc
      rw [Hchk] at hc
      cases eff with
      | mkEffectU ret ws zs us cs ci =>
        cases ws with
        | cons _ _ => simp at hc
        | nil =>
        cases zs with
        | cons _ _ => simp at hc
        | nil =>
        cases us with
        | cons _ _ => simp at hc
        | nil =>
        cases cs with
        | cons _ _ => simp at hc
        | nil =>
          dsimp only at hc
          -- the three gates, then the copy-in ledger, then the answer
          by_cases hgate : (decide (1 ≤ ((ret.toNat : Nat) : Int))
              && decide (((ret.toNat : Nat) : Int) ≤ iovs_total iovs)
              && !(addr_is_error_b ret)) = true
          · rw [ite_eq_left hgate] at hc
            by_cases hci : access_ranges_eqb ci
                (import_iovecs_accesses (ms_read_byte ms) iov (BitVec.ofInt 64 (iovs.length : Int))
                  ++ iov_prefix_accesses iovs ret.toNat) = true
            · rw [ite_eq_left hci] at hc
              cases hc
              have hg := hgate
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
              obtain ⟨⟨hg1, hg2⟩, _⟩ := hg
              have hci' := (access_ranges_eqb_eq ci _).mp hci
              refine ⟨⟨ret.toNat, by omega, ?_⟩, ?_, rfl, rfl⟩
              · omega
              · dsimp only [effs]
                rw [u64_roundtrip' ret, hci']
            · rw [ite_eq_right hci] at hc
              exact absurd hc (by simp)
          · rw [ite_eq_right hgate] at hc
            exact absurd hc (by simp)
    rcases sstep_svc_inv segs ms model x8 e st Hsvc hss with
      ⟨eff, model', ev, hc, harm⟩ | ⟨eff, hc, he, hst⟩
    · rcases harm with ⟨m'', hh', he, hmat, hst⟩ | ⟨hh', he, hmat, hst⟩
                     | ⟨code, hh', he, hks, hst⟩
      · obtain ⟨i, heff, hm, hev⟩ := Hinv eff model' ev hc
        subst heff
        rw [hm] at hmat
        subst hev
        rw [materialize_model_accesses_no_lazy model _ Hlazy] at hmat
        obtain rfl := Option.some.inj hmat
        refine ⟨i, he, ?_⟩
        rw [hst, show apply_effect ms (effs i)
              = set_gpr0 ms (BitVec.ofInt 64 (i.1 : Int)) from by
            dsimp only [effs]
            exact apply_effect_copyins_no_write ms _ _]
      · obtain ⟨i, heff, hm, hev⟩ := Hinv eff model' ev hc
        rw [hm] at hmat
        rw [materialize_model_accesses_no_lazy model _ Hlazy] at hmat
        simp at hmat
      · obtain ⟨i, heff, hm, hev⟩ := Hinv eff model' ev hc
        rw [hm] at hh'
        rw [Hh] at hh'
        simp at hh'
    · exfalso
      rw [Hchk] at hc
      cases eff with
      | mkEffectU ret ws zs us cs ci =>
        cases ws with
        | cons _ _ => simp at hc
        | nil =>
        cases zs with
        | cons _ _ => simp at hc
        | nil =>
        cases us with
        | cons _ _ => simp at hc
        | nil =>
        cases cs with
        | cons _ _ => simp at hc
        | nil =>
          dsimp only at hc
          by_cases hgate : (decide (1 ≤ ((ret.toNat : Nat) : Int))
              && decide (((ret.toNat : Nat) : Int) ≤ iovs_total iovs)
              && !(addr_is_error_b ret)) = true
          · rw [ite_eq_left hgate] at hc
            by_cases hci : access_ranges_eqb ci
                (import_iovecs_accesses (ms_read_byte ms) iov (BitVec.ofInt 64 (iovs.length : Int))
                  ++ iov_prefix_accesses iovs ret.toNat) = true
            · rw [ite_eq_left hci] at hc
              exact absurd hc (by simp)
            · rw [ite_eq_right hci] at hc
              exact absurd hc (by simp)
          · rw [ite_eq_right hgate] at hc
            exact absurd hc (by simp)


/-- ONE iovec (musl: nothing buffered, `iov = &iovs[1]`, `iovcnt = 1`). -/
theorem rz_writev1 (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int) (iov b1 n1 : word)
    (bs1 : List byte) (T : Nat → TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 1)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Hiok : (iov.toNat : Int) + 16 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int)) (_Htmax : (n1.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) ≤ 2 ^ 30)
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ bs1.length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model) (T k)) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_alt (fun i : wr_index bs1 =>
         t_emit ((bs1.take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) (T i.1))) := by
  have hno : (getr regs 17).toNat = 66 := by
    rw [H17]; exact u64_lit 66 (by omega) (by omega)
  have hp : realizes segs (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
      (t_alt (fun i : wr_index bs1 =>
         t_emit ((bs1.take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) (T i.1))) := by
    have hraw := rz_writev_pending segs (epend regs pc mem (seg_rom segs) (getr regs 17))
      (getr regs 17) model fd iov [(b1, n1)] [bs1] T
      rfl Hh Hlazy rfl Hfd Hfdr hno
      (by rw [ms_gpr_epend0]; exact H10)
      (by rw [ms_gpr_epend1]; exact H11)
      (by rw [ms_gpr_epend2, H12]; rfl)
      (by exact ⟨by simp, by simp⟩)
      (by simpa using Hiok)
      (by
        refine ⟨Rb1, Rn1, ?_, trivial⟩
        show (n1.toNat : Int) < 2 ^ 63
        omega)
      (by exact ⟨Hb1, trivial⟩)
      (by exact ⟨Rs1, trivial⟩)
      (by simpa [iovs_total] using Ht1) (by simpa [iovs_total] using _Htmax)
      (by simpa [iovs_total] using Ht30)
      (by
        intro k hk1 hk2
        rw [adv_set_epend]
        exact Hk k hk1 (by simpa using hk2))
    have hfl : ([bs1] : List (List byte)).flatten = bs1 := List.append_nil bs1
    rw [hfl] at hraw
    exact hraw
  exact rz_sys segs regs pc mem (seg_rom segs) model w _ Hh Hlazy HF HE hp


/-- From the `mkst` state on the ecall, TWO iovecs (musl: buffered bytes +
    the new data; the second may be empty, e.g. the final flush
    `f->write(f, 0, 0)` passes `[{wbase, n1}, {NULL, 0}]`).  The three
    `TASK_SIZE` premises are the import path's range tests: a binary's iovec
    array and buffers are stack, image or allocator addresses far below
    `State.TASK_SIZE` = 2^47, so each costs the caller one `omega`. -/
theorem rz_writev2 (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int)
    (iov b1 n1 b2 n2 : word) (bs1 bs2 : List byte) (T : Nat → TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 2)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rb2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 16)) 8
             = some (word_to_le_bytes 8 b2))
    (Rn2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 24)) 8
             = some (word_to_le_bytes 8 n2))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Rs2 : rdn segs mem b2 n2.toNat = some bs2)
    (Hiok : (iov.toNat : Int) + 32 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Hb2 : (b2.toNat : Int) + (n2.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int) + (n2.toNat : Int))
    (_Htmax : (n1.toNat : Int) + (n2.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) + (n2.toNat : Int) ≤ 2 ^ 30)
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ (bs1 ++ bs2).length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model) (T k)) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_alt (fun i : wr_index (bs1 ++ bs2) =>
         t_emit (((bs1 ++ bs2).take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) (T i.1))) := by
  have hno : (getr regs 17).toNat = 66 := by
    rw [H17]; exact u64_lit 66 (by omega) (by omega)
  -- the second descriptor sits at `iov + 16`, so its length at `iov + 24`
  have hTASK64 : TASK_SIZE < 2 ^ 64 := by unfold TASK_SIZE; decide
  have h16 : (BitVec.ofInt 64 ((iov.toNat : Int) + 16)).toNat = iov.toNat + 16 :=
    u64_lit _ (by omega) (by omega)
  have hat : (BitVec.ofInt 64 ((BitVec.ofInt 64 ((iov.toNat : Int) + 16)).toNat + 8))
      = BitVec.ofInt 64 ((iov.toNat : Int) + 24) := by
    rw [h16]
    congr 1
  have hraw := rz_writev_pending segs (epend regs pc mem (seg_rom segs) (getr regs 17))
    (getr regs 17) model fd iov [(b1, n1), (b2, n2)] [bs1, bs2] T
    rfl Hh Hlazy rfl Hfd Hfdr hno
    (by rw [ms_gpr_epend0]; exact H10)
    (by rw [ms_gpr_epend1]; exact H11)
    (by rw [ms_gpr_epend2, H12]; rfl)
    (by exact ⟨by simp, by simp⟩)
    (by simpa using Hiok)
    (by
      refine ⟨Rb1, Rn1, ?_, Rb2, ?_, ?_, trivial⟩
      · have : (n1.toNat : Int) < 2 ^ 63 := by omega
        simpa using this
      · exact hat.symm ▸ Rn2
      · show (n2.toNat : Int) < 2 ^ 63
        omega)
    (by exact ⟨Hb1, ⟨Hb2, trivial⟩⟩)
    (by exact ⟨Rs1, ⟨Rs2, trivial⟩⟩)
    (by simpa [iovs_total] using Ht1) (by simpa [iovs_total] using _Htmax)
    (by simpa [iovs_total] using Ht30)
    (by
      intro k hk1 hk2
      rw [adv_set_epend]
      exact Hk k hk1 (by simpa using hk2))
  have hfl : ([bs1, bs2] : List (List byte)).flatten = bs1 ++ bs2 := by
    simp
  rw [hfl] at hraw
  exact rz_sys segs regs pc mem (seg_rom segs) model w _ Hh Hlazy HF HE hraw

/-- The LOOP-facing corollary: if, after each delivery of `k` bytes, the
    remainder of `__stdio_write` (re-issue on the rest, then return)
    realizes "emit the undelivered suffix, then `K`", the call site realizes
    the full emission.  Short writes leave no trace. -/
theorem rz_writev2_wall (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int)
    (iov b1 n1 b2 n2 : word) (bs1 bs2 : List byte) (K : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 2)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rb2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 16)) 8
             = some (word_to_le_bytes 8 b2))
    (Rn2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 24)) 8
             = some (word_to_le_bytes 8 n2))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Rs2 : rdn segs mem b2 n2.toNat = some bs2)
    (Hiok : (iov.toNat : Int) + 32 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Hb2 : (b2.toNat : Int) + (n2.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int) + (n2.toNat : Int))
    (_Htmax : (n1.toNat : Int) + (n2.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) + (n2.toNat : Int) ≤ 2 ^ 30)
    (HK : K [])
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ (bs1 ++ bs2).length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (((bs1 ++ bs2).drop k).map (.WriteEv (BitVec.ofInt 64 fd))) K)) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_emit ((bs1 ++ bs2).map (.WriteEv (BitVec.ofInt 64 fd))) K) := by
  -- the checker's own length guarantee pins the delivered total
  have L1 : bs1.length = n1.toNat := rdn_length segs mem n1.toNat b1 bs1 Rs1
  have L2 : bs2.length = n2.toNat := rdn_length segs mem n2.toNat b2 bs2 Rs2
  have hnb : 1 ≤ (bs1 ++ bs2).length := by
    rw [List.length_append, L1, L2]; omega
  refine rz_wall segs _ (BitVec.ofInt 64 fd) (bs1 ++ bs2) K hnb HK ?_
  exact rz_writev2 segs regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
    (fun k => t_emit (((bs1 ++ bs2).drop k).map (.WriteEv (BitVec.ofInt 64 fd))) K)
    HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok
    Hb1 Hb2 Ht1 _Htmax Ht30 Hk

/-- The same for ONE iovec. -/
theorem rz_writev1_wall (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int) (iov b1 n1 : word)
    (bs1 : List byte) (K : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 1)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Hiok : (iov.toNat : Int) + 16 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int)) (_Htmax : (n1.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) ≤ 2 ^ 30)
    (HK : K [])
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ bs1.length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit ((bs1.drop k).map (.WriteEv (BitVec.ofInt 64 fd))) K)) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_emit (bs1.map (.WriteEv (BitVec.ofInt 64 fd))) K) := by
  have L1 : bs1.length = n1.toNat := rdn_length segs mem n1.toNat b1 bs1 Rs1
  have hnb : 1 ≤ bs1.length := by rw [L1]; omega
  refine rz_wall segs _ (BitVec.ofInt 64 fd) bs1 K hnb HK ?_
  exact rz_writev1 segs regs pc mem model w fd iov b1 n1 bs1
    (fun k => t_emit ((bs1.drop k).map (.WriteEv (BitVec.ofInt 64 fd))) K)
    HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1 Hiok
    Hb1 Ht1 _Htmax Ht30 Hk

/-- The FULL-delivery special case as a plain continuation: if the code
    after the syscall does not care how much was delivered (musl loops; this
    form is for callers that re-establish the same `K` from every
    post-state, e.g. by re-entering the loop), the shape is `t_write_ch`. -/
theorem rz_writev2_ch (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int)
    (iov b1 n1 b2 n2 : word) (bs1 bs2 : List byte) (K : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 2)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rb2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 16)) 8
             = some (word_to_le_bytes 8 b2))
    (Rn2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 24)) 8
             = some (word_to_le_bytes 8 n2))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Rs2 : rdn segs mem b2 n2.toNat = some bs2)
    (Hiok : (iov.toNat : Int) + 32 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Hb2 : (b2.toNat : Int) + (n2.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int) + (n2.toNat : Int))
    (_Htmax : (n1.toNat : Int) + (n2.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) + (n2.toNat : Int) ≤ 2 ^ 30)
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ (bs1 ++ bs2).length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model) K) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_write_ch (BitVec.ofInt 64 fd) (bs1 ++ bs2) K) := by
  unfold t_write_ch
  exact rz_writev2 segs regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)
    HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok
    Hb1 Hb2 Ht1 _Htmax Ht30 Hk

end WithSegsPending


/-! =========================================================================
    REMAINING — the one declaration still deferred
    =========================================================================

    `rz_writev1_zero`, the degenerate zero-total `writev(fd, [{b1, 0}], 1)`
    that musl's `f->write(f, 0, 0)` issues when nothing is buffered: the
    checker answers `ret_only_copyins [(iov, 16)] 0 model []`, so the call is
    deterministic, silent, and returns 0.  Everything it needs is in the tree
    now (the eight proved siblings above, `import_iovecs_of_array`'s
    `nr_segs == 1` short circuit, `import_iovecs_accesses`,
    `check_ret_only_copyins_ok_iff` and the `adv_set_epend` bridge); it is
    deferred only for lack of a worked proof.  The `Hmax` premise is `rw_bytes_max`'s
    non-negativity and, like `writev_check`'s `_Htmax`, stays a premise for
    the callers' sake.) -/

end LinuxSem.Common.LibWritev











