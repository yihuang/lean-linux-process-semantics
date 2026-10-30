/-
  * Common.RefEnframeArith — pure arithmetic for the [enframe] summary
    (no machine semantics beyond PropExec's value shapes).

    - literal forms of [v_and]/[v_or]/[v_andi]/[v_srli]/[v_slli]/[v_mul]/[v_sltu],
      [not] ([v_xori _ (-1)]), and the 32-bit ops [subw]/[addw]/[slliw] on
      small values;
    - bit-field extraction from mallocng's packed meta word
      [W = last_idx + 32*freeable + 64*sizeclass + 4096*maplen];
    - the slot-offset computation [enframe_off] and its bound [<= slack].

  NOTES.

  - `Z` is `Int`, `N`/`nat` are `Nat`, `list` is `List`, `Z_to_bv 64 z` is
    `BitVec.ofInt 64 z`, and `bv_unsigned w` is the `Int`-valued
    `(w.toNat : Int)` spelling the rest of the `Common` tree uses.
  - `Z.land`/`Z.lor` have no Lean-core counterpart on `Int` (there is no
    `Int.land`), so this tree uses `PropExec.zland`/`zlor` (through `Nat`,
    whose definitions are literally the `Sys.Uapi.z_land`/`z_lor` that
    `MallocDefs.smear`/`enframe_off` are written with).  They agree with
    `Z.land`/`Z.lor` on non-negative operands, which is every operand in
    this file.
  - `Z.testbit` does not exist on Lean's `Int`, so the bit-level lemmas
    ([fld_hi], [lor_shift5], [u_not]) are stated and proved on the `Nat`
    representatives through `Nat.testBit` — the same place `Z.testbit` is
    defined .
 Literal exponents (`2 ^ 5`, `2 ^ 64`)
    are unchanged.
  - `Z.ones` is likewise absent; the masks  builds with it are
    `2 ^ k - 1`, which is how they are written here.
-/
import LinuxSem.Common.AgentLib
import LinuxSem.Common.MallocDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LinuxSem.Common.RefEnframeArith

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.Common.PropExec
open LinuxSem.Common.AgentLib
open LinuxSem.Common.MallocDefs
open LinuxSem.LinuxProcessSem.Sys.Uapi (z_land z_lor)

/-! =========================================================================
    Literal forms of the value shapes
    ========================================================================= -/

theorem v_and_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    v_and (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = BitVec.ofInt 64 (zland a b) := by
  unfold v_and
  rw [u64_lit a Ha, u64_lit b Hb]

theorem v_or_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    v_or (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = BitVec.ofInt 64 (zlor a b) := by
  unfold v_or
  rw [u64_lit a Ha, u64_lit b Hb]

theorem v_andi_lit (a i : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hi : 0 ≤ i ∧ i < 2 ^ 64) :
    v_andi (BitVec.ofInt 64 a) i = BitVec.ofInt 64 (zland a i) := by
  have hw : bv_wrap 64 i = i := by
    unfold bv_wrap
    rw [two_pow64_cast, Int.emod_eq_of_lt Hi.1 Hi.2]
  unfold v_andi
  rw [u64_lit a Ha, hw]

theorem v_srli_lit (a s : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hs : 0 ≤ s) :
    v_srli (BitVec.ofInt 64 a) s = BitVec.ofInt 64 (a / ((2 ^ s.toNat : Nat) : Int)) := by
  unfold v_srli zshiftr
  rw [u64_lit a Ha]

theorem v_slli_lit (a s : Int) (Ha : 0 ≤ a) (Hs : 0 ≤ s)
    (H : a * ((2 ^ s.toNat : Nat) : Int) < 2 ^ 64) :
    v_slli (BitVec.ofInt 64 a) s
      = BitVec.ofInt 64 (a * ((2 ^ s.toNat : Nat) : Int)) := by
  have hspos : (0 : Int) < ((2 ^ s.toNat : Nat) : Int) := by
    have := Nat.two_pow_pos s.toNat
    omega
  have hle : a ≤ a * ((2 ^ s.toNat : Nat) : Int) := by
    have he1 : (1 : Int) ≤ ((2 ^ s.toNat : Nat) : Int) := by omega
    have h := Int.mul_le_mul_of_nonneg_left he1 Ha
    simpa using h
  have Ha' : 0 ≤ a ∧ a < 2 ^ 64 := by omega
  unfold v_slli zshiftl
  rw [u64_lit a Ha']

theorem v_mul_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    v_mul (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = BitVec.ofInt 64 (a * b) := by
  unfold v_mul
  rw [u64_lit a Ha, u64_lit b Hb]

theorem v_sltu_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    v_sltu (BitVec.ofInt 64 a) (BitVec.ofInt 64 b)
      = BitVec.ofInt 64 (if decide (a < b) then 1 else 0) := by
  have hc : c_ltu (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a < b) :=
    c_ltu_lit a b Ha Hb
  unfold v_sltu
  rw [hc]
  by_cases h : a < b <;> simp [h]

/-! Bounds of [land]/[lor] results. -/

theorem land_range (a b : Int) (Ha : 0 ≤ a) (Hb : 0 ≤ b) :
    0 ≤ zland a b ∧ zland a b ≤ a := by
  have ha : (a.toNat : Int) = a := Int.toNat_of_nonneg Ha
  unfold zland
  have h1 : ((a.toNat &&& b.toNat : Nat) : Int) ≤ (a.toNat : Int) := by
    exact Int.ofNat_le.mpr (Nat.and_le_left)
  have h2 : (0 : Int) ≤ ((a.toNat &&& b.toNat : Nat) : Int) := by
    exact Int.natCast_nonneg _
  omega

/-- the width is a `Nat` here .  Lean has no
    `2 ^ (k : Int)` — there is no `HPow Int Int Int` — and every call site
    passes a literal width, so nothing is lost. -/
theorem lor_range (a b : Int) (k : Nat)
    (Ha : 0 ≤ a ∧ a < (2 : Int) ^ k) (Hb : 0 ≤ b ∧ b < (2 : Int) ^ k) :
    0 ≤ zlor a b ∧ zlor a b < (2 : Int) ^ k := by
  have hk : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := Int.natCast_pow 2 k
  have ha : a.toNat < 2 ^ k := by
    refine Int.ofNat_lt.mp ?_
    rw [Int.toNat_of_nonneg Ha.1]
    rw [hk]; exact Ha.2
  have hb : b.toNat < 2 ^ k := by
    refine Int.ofNat_lt.mp ?_
    rw [Int.toNat_of_nonneg Hb.1]
    rw [hk]; exact Hb.2
  have h3 : (a.toNat ||| b.toNat) < 2 ^ k := Nat.or_lt_two_pow ha hb
  unfold zlor
  constructor
  · exact Int.natCast_nonneg _
  · rw [← hk]
    exact Int.ofNat_lt.mpr h3

/-! [not] = [xori rd, rs, -1]: the unsigned value. -/

/-- The complement identity behind [u_not]: within `k` bits, `xor` with
    `2^k - 1` is the complement.   -/
theorem xor_two_pow_sub_one (n k : Nat) (hn : n < 2 ^ k) :
    n ^^^ (2 ^ k - 1) = 2 ^ k - 1 - n := by
  have hsub : 2 ^ k - 1 - n = 2 ^ k - (n + 1) := by omega
  rw [hsub]
  have hik : ∀ i, Nat.testBit n i = true → i < k := by
    intro i hi
    rcases Nat.lt_or_ge i k with h | h
    · exact h
    · have h2 : n < 2 ^ i := by
        have h1 : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) h
        omega
      rw [Nat.testBit_lt_two_pow h2] at hi
      exact Bool.noConfusion hi
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_succ hn]
  by_cases hki : i < k
  · cases hb : Nat.testBit n i <;> simp [hki]
  · have hb : Nat.testBit n i = false := by
      have h1 : n < 2 ^ i := by
        have h2 : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      exact Nat.testBit_lt_two_pow h1
    simp [hki, hb]

theorem u_not (s : Int) (Hs : 0 ≤ s ∧ s < 2 ^ 64) :
    ((v_xori (BitVec.ofInt 64 s) (-1)).toNat : Int) = 2 ^ 64 - 1 - s := by
  have hm1 : bv_wrap 64 (-1) = 2 ^ 64 - 1 := by
    unfold bv_wrap
    rw [two_pow64_cast]
    rw [show (-1 : Int) = (2 ^ 64 - 1) + 2 ^ 64 * (-1) from by omega,
      Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (a := 2 ^ 64 - 1) (b := 2 ^ 64) (by omega) (by omega)]
  have hs64 : s.toNat < 2 ^ 64 := by
    have h := Hs.2
    have h2 : (s.toNat : Int) = s := Int.toNat_of_nonneg Hs.1
    omega
  have htoNat : ((2 ^ 64 : Int) - 1).toNat = 2 ^ 64 - 1 := by decide
  have hxm : zlxor ((BitVec.ofInt 64 s).toNat : Int) (bv_wrap 64 (-1))
      = ((s.toNat ^^^ (2 ^ 64 - 1) : Nat) : Int) := by
    rw [hm1]
    unfold zlxor
    rw [u64_lit s Hs, htoNat]
  have hkey : s.toNat ^^^ (2 ^ 64 - 1) = 2 ^ 64 - 1 - s.toNat :=
    xor_two_pow_sub_one s.toNat 64 hs64
  unfold v_xori
  rw [hxm, hkey]
  rw [u64_lit]
  · rw [Int.ofNat_sub (by omega : s.toNat ≤ 2 ^ 64 - 1),
      show (((2 ^ 64 - 1 : Nat)) : Int) = (2 : Int) ^ 64 - 1 from by decide,
      Int.toNat_of_nonneg Hs.1]
  · constructor <;> omega

/-! =========================================================================
    32-bit operations on small values
    ========================================================================= -/

theorem swrap32_small (x : Int) (Hx : -2 ^ 31 ≤ x ∧ x < 2 ^ 31) : bv_swrap 32 x = x := by
  unfold bv_swrap
  have h1 : ((2 ^ (32 - 1) : Nat) : Int) = 2 ^ 31 := by decide
  have h2 : ((2 ^ 32 : Nat) : Int) = 2 ^ 32 := by decide
  rw [h1, h2, Int.emod_eq_of_lt (a := x + 2 ^ 31) (b := 2 ^ 32) (by omega) (by omega)]
  omega

theorem swrap32_add_mod (x k : Int) : bv_swrap 32 (x + k * 2 ^ 32) = bv_swrap 32 x := by
  unfold bv_swrap
  have h32 : ((2 ^ (32 - 1) : Nat) : Int) = 2 ^ 31 := by decide
  have h64 : ((2 ^ 32 : Nat) : Int) = 2 ^ 32 := by decide
  rw [h32, h64]
  rw [show x + k * 2 ^ 32 + 2 ^ 31 = (x + 2 ^ 31) + 2 ^ 32 * k from by omega,
    Int.add_mul_emod_self_left]

theorem v_subw_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64)
    (H : -2 ^ 31 ≤ a - b ∧ a - b < 2 ^ 31) :
    v_subw (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = BitVec.ofInt 64 (a - b) := by
  unfold v_subw
  rw [u64_lit a Ha, u64_lit b Hb, swrap32_small (a - b) H]

theorem v_slliw_lit (a s : Int) (Ha : 0 ≤ a) (Hs : 0 ≤ s)
    (H : a * ((2 ^ s.toNat : Nat) : Int) < 2 ^ 31) :
    v_slliw (BitVec.ofInt 64 a) s
      = BitVec.ofInt 64 (a * ((2 ^ s.toNat : Nat) : Int)) := by
  have hspos : (0 : Int) < ((2 ^ s.toNat : Nat) : Int) := by
    have := Nat.two_pow_pos s.toNat
    omega
  have hle : a ≤ a * ((2 ^ s.toNat : Nat) : Int) := by
    have he1 : (1 : Int) ≤ ((2 ^ s.toNat : Nat) : Int) := by omega
    have h := Int.mul_le_mul_of_nonneg_left he1 Ha
    simpa using h
  have hnn : 0 ≤ a * ((2 ^ s.toNat : Nat) : Int) := Int.mul_nonneg Ha (Int.le_of_lt hspos)
  have Ha' : 0 ≤ a ∧ a < 2 ^ 64 := by omega
  unfold v_slliw zshiftl
  rw [u64_lit a Ha']
  rw [swrap32_small (a * ((2 ^ s.toNat : Nat) : Int)) (by constructor <;> omega)]

theorem v_addw_small (x y : word) (r : Int) (Hr : -2 ^ 31 ≤ r ∧ r < 2 ^ 31)
    (H : ∃ k, ((x.toNat : Int) + (y.toNat : Int)) = r + k * 2 ^ 32) :
    v_addw x y = BitVec.ofInt 64 r := by
  obtain ⟨k, Hk⟩ := H
  unfold v_addw
  rw [Hk, swrap32_add_mod, swrap32_small r Hr]

/-! =========================================================================
    Bit fields of the packed meta word W (MallocDefs.w_lastidx & co.)
    ========================================================================= -/

/-- `andi a5,a4,31` — needs the non-negativity that `Z.land` has for free
    (Lean's `zland` goes through `toNat`). -/
theorem fld_lastidx (W : Int) (HW : 0 ≤ W) : zland W 31 = W % 32 := by
  unfold zland
  have hW : (W.toNat : Int) = W := Int.toNat_of_nonneg HW
  have h31 : (Int.toNat 31 : Nat) = 2 ^ 5 - 1 := by decide
  rw [h31, Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod]
  rw [show ((2 : Nat) ^ 5) = 32 from by decide, hW]
  omega

/-! =========================================================================
    Bit fields of the packed meta word W (MallocDefs.w_lastidx & co.)
    ========================================================================= -/

/-- `srli a4,a4,5; andi a4,a4,126` = 2 * sizeclass — the brute-force check
     runs over the 128 residues. -/
theorem land_126_check :
    zall 128 (fun r => decide (zland r 126 = 2 * ((r / 2) % 64))) 0 = true := by
  decide

/-- `126 &&& 127 = 126`, so masking with 126 only looks at the low 7 bits:
    the residue modulo 128 is all [land_126] has to see. -/
theorem and_126_mod128 (n : Nat) : n &&& 126 = (n % 128) &&& 126 := by
  conv => lhs; rw [show (126 : Nat) = 127 &&& 126 from by decide]
  rw [← Nat.and_assoc, show (127 : Nat) = 2 ^ 7 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod, show (2 : Nat) ^ 7 = 128 from by decide]

theorem land_126 (x : Int) (Hx : 0 ≤ x) : zland x 126 = 2 * ((x / 2) % 64) := by
  have hstep1 : zland x 126 = zland (x % 128) 126 := by
    unfold zland
    rw [show (Int.toNat 126 : Nat) = 126 from by decide, and_126_mod128 x.toNat]
    have h128 : x.toNat % 128 = (x % 128).toNat := by omega
    rw [h128]
  rw [hstep1]
  have hz : zland (x % 128) 126 = 2 * (((x % 128) / 2) % 64) := by
    have := zallN_spec 128 (fun r => decide (zland r 126 = 2 * ((r / 2) % 64)))
      land_126_check (x % 128) ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
    exact of_decide_eq_true this
  rw [hz]
  congr 1
  omega

theorem fld_sizeclass2 (W : Int) (HW : 0 ≤ W) :
    zland (W / 32) 126 = 2 * ((W / 64) % 64) := by
  rw [land_126 (W / 32) (Int.ediv_nonneg HW (by omega))]
  congr 1
  omega

/-- `lui a5,0xfffff; and a4,a4,a5` = 4096 * maplen.  the bits
    live on Lean's `Nat` (no `Int.testBit`); the mask's bits are
    `12 <= i < 64` and both sides are shown to have bit `i` equal to
    `testBit W.toNat i` once `12 ≤ i`. -/
theorem fld_hi (W : Int) (HW : 0 ≤ W ∧ W < 2 ^ 64) :
    zland W (2 ^ 64 - 4096) = 4096 * (W / 4096) := by
  have hW : (W.toNat : Int) = W := Int.toNat_of_nonneg HW.1
  have h64 : W.toNat < 2 ^ 64 := by
    have := HW.2; omega
  have hmask : ((2 ^ 64 - 4096 : Int)).toNat = 2 ^ 64 - 4096 := by decide
  have hpow : (2 : Nat) ^ 12 = 4096 := by decide
  have hm_eq : (2 : Nat) ^ 64 - 4096 = 2 ^ 64 - (2 ^ 12 - 1 + 1) := by omega
  have hsmall : (2 : Nat) ^ 12 - 1 < 2 ^ 64 := by
    have : (2 : Nat) ^ 12 = 4096 := by decide
    have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    omega
  have hmask_bit : ∀ j : Nat, (2 ^ 64 - 4096).testBit j
      = (decide (12 ≤ j) && decide (j < 64)) := by
    intro j
    rw [hm_eq, Nat.testBit_two_pow_sub_succ hsmall j, Nat.testBit_two_pow_sub_one]
    by_cases hj : j < 12
    · have h1 : ¬ (12 ≤ j) := by omega
      simp [hj, h1]
    · have h1 : 12 ≤ j := by omega
      by_cases hj2 : j < 64
      · simp [hj, h1, hj2]
      · simp [hj, h1, hj2]
  have hnat : W.toNat &&& (2 ^ 64 - 4096) = (W.toNat / 4096) * 4096 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, hmask_bit i, ← hpow, Nat.testBit_mul_two_pow]
    by_cases h12 : i < 12
    · have h1 : ¬ (12 ≤ i) := by omega
      simp [h12, h1]
    · have h1 : 12 ≤ i := by omega
      have hdiv : (W.toNat / 2 ^ 12).testBit (i - 12) = W.toNat.testBit i := by
        rw [Nat.testBit_div_two_pow, show i - 12 + 12 = i from by omega]
      rcases Nat.lt_or_ge i 64 with hi | hi
      · simp [h12, h1, hi, hdiv]
      · have hw : W.toNat.testBit i = false := by
          apply Nat.testBit_lt_two_pow
          have h2 : (2 : Nat) ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
          omega
        simp [h12, h1, hi, hdiv, hw]
  unfold zland
  rw [hmask, hnat]
  have hdiv : (W / 4096 : Int) = ((W.toNat / 4096 : Nat) : Int) := by omega
  rw [hdiv, show (4096 : Int) = ((4096 : Nat) : Int) from rfl, ← Int.natCast_mul, Nat.mul_comm]

/-- The final header byte: `idx | rc << 5`. -/
theorem lor_shift5 (rc l : Int) (Hrc : 0 ≤ rc) (Hl : 0 ≤ l ∧ l < 32) :
    zlor (rc * 2 ^ 5) l = l + 32 * rc := by
  have hrc : (rc.toNat : Int) = rc := Int.toNat_of_nonneg Hrc
  have hl : (l.toNat : Int) = l := Int.toNat_of_nonneg Hl.1
  have hln : l.toNat < 32 := by omega
  have hnat : (rc.toNat * 32 ||| l.toNat) = l.toNat + 32 * rc.toNat := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 5) (by omega : l.toNat < 2 ^ 5) rc.toNat
    rw [show (2 : Nat) ^ 5 = 32 from by decide, Nat.mul_comm (32) rc.toNat] at h
    rw [← h, Nat.add_comm, Nat.mul_comm rc.toNat 32]
  have hval : ((rc * 2 ^ 5 : Int)).toNat = rc.toNat * 32 := by
    have h1 : rc * 2 ^ 5 = (((rc.toNat * 32 : Nat)) : Int) := by
      conv => lhs; rw [← hrc]
      rw [show (2 : Int) ^ 5 = ((32 : Nat) : Int) from by decide, ← Int.natCast_mul]
    rw [h1]
    exact Int.toNat_natCast _
  unfold zlor
  rw [hval, hnat]
  push_cast
  rw [hl, hrc]

theorem land_31_small (l : Int) (H : 0 ≤ l ∧ l < 32) : zland l 31 = l := by
  unfold zland
  rw [show (Int.toNat 31 : Nat) = 2 ^ 5 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod,
    show ((2 : Nat) ^ 5) = 32 from by decide, Int.toNat_of_nonneg H.1]
  omega

theorem land_255 (a : Int) (H : 0 ≤ a) : zland a 255 = a % 256 := by
  unfold zland
  rw [show (Int.toNat 255 : Nat) = 2 ^ 8 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod,
    show ((2 : Nat) ^ 8) = 256 from by decide, Int.toNat_of_nonneg H]
  omega

/-! =========================================================================
    The slot offset
    ========================================================================= -/

/- [smear] / [enframe_off] : see MallocDefs. -/

/-- [smear] of a small value stays below twice it: it is the smallest `2^k - 1`
    at or above its argument.  Checked by evaluation over the 256 values
    [enframe_off] needs. -/
theorem smear_small_check :
    zall 256 (fun s => decide (0 ≤ smear s) && decide (smear s ≤ 2 * s)) 0 = true := by
  decide

/-- Below 256 the masked candidate is at most [smear slack ≤ 2 * slack], so
    subtracting [slack + 1] from one above [slack] lands in `[0, slack)`. -/
theorem enframe_off_small (slack off0 : Int) (Hs : 0 ≤ slack ∧ slack < 256) (Ho : 0 ≤ off0) :
    0 ≤ enframe_off slack off0 ∧ enframe_off slack off0 ≤ slack := by
  have H := zallN_spec 256 (fun s => decide (0 ≤ smear s) && decide (smear s ≤ 2 * s))
    smear_small_check slack Hs
  have h0 : 0 ≤ smear slack := of_decide_eq_true (Bool.and_eq_true_iff.mp H).1
  have h2 : smear slack ≤ 2 * slack := of_decide_eq_true (Bool.and_eq_true_iff.mp H).2
  have hom : 0 ≤ z_land off0 (smear slack) ∧ z_land off0 (smear slack) ≤ smear slack := by
    have hle : off0.toNat &&& (smear slack).toNat ≤ (smear slack).toNat := Nat.and_le_right
    simp only [z_land]
    omega
  unfold enframe_off
  dsimp only
  split
  · omega
  · split <;> omega

/-- The two conclusions the callers need: non-negative, at most `max slack off0`,
    and either within `slack` or exactly the candidate `off0`. -/
theorem enframe_off_bound (slack off0 : Int) (Hs : 0 ≤ slack)
    (Ho : 0 ≤ off0 ∧ off0 < 256) :
    0 ≤ enframe_off slack off0 ∧ enframe_off slack off0 ≤ max slack off0
      ∧ (enframe_off slack off0 ≤ slack ∨ enframe_off slack off0 = off0) := by
  by_cases hl : slack < 256
  · obtain ⟨h1, h2⟩ := enframe_off_small slack off0 ⟨Hs, hl⟩ Ho.1
    exact ⟨h1, ⟨by omega, Or.inl h2⟩⟩
  · have hle : off0 ≤ slack := by omega
    have hoff : enframe_off slack off0 = off0 := by
      unfold enframe_off
      rw [ite_eq_left hle]
    refine ⟨by rw [hoff]; exact Ho.1, ⟨by rw [hoff]; omega, Or.inr hoff⟩⟩

theorem enframe_off_le (slack off0 : Int) (Hs : 0 ≤ slack)
    (Ho : 0 ≤ off0 ∧ off0 < 256) :
    0 ≤ enframe_off slack off0 ∧ enframe_off slack off0 ≤ slack := by
  by_cases hl : slack < 256
  · exact enframe_off_small slack off0 ⟨Hs, hl⟩ Ho.1
  · have hle : off0 ≤ slack := by omega
    have hoff : enframe_off slack off0 = off0 := by
      unfold enframe_off
      rw [ite_eq_left hle]
    rw [hoff]
    exact ⟨Ho.1, hle⟩

theorem smear_range (slack : Int) (Hs : 0 ≤ slack ∧ slack < 2 ^ 64) :
    0 ≤ smear slack ∧ smear slack < 2 ^ 64 := by
  have hs2 : 0 ≤ slack / 2 ∧ slack / 2 < (2 : Int) ^ 64 := by
    refine ⟨Int.ediv_nonneg Hs.1 (by omega), ?_⟩
    have := Int.ediv_le_self 2 Hs.1
    omega
  have hm1 := lor_range slack (slack / 2) 64 ⟨Hs.1, Hs.2⟩ ⟨hs2.1, hs2.2⟩
  have hs4 : 0 ≤ zlor slack (slack / 2) / 4 ∧ zlor slack (slack / 2) / 4 < (2 : Int) ^ 64 := by
    refine ⟨Int.ediv_nonneg hm1.1 (by omega), ?_⟩
    have := Int.ediv_le_self 4 hm1.1
    omega
  have hm2 := lor_range (zlor slack (slack / 2)) (zlor slack (slack / 2) / 4) 64
    ⟨hm1.1, hm1.2⟩ ⟨hs4.1, hs4.2⟩
  have hs16 : 0 ≤ zlor (zlor slack (slack / 2)) (zlor slack (slack / 2) / 4) / 16 ∧
      zlor (zlor slack (slack / 2)) (zlor slack (slack / 2) / 4) / 16 < (2 : Int) ^ 64 := by
    refine ⟨Int.ediv_nonneg hm2.1 (by omega), ?_⟩
    have := Int.ediv_le_self 16 hm2.1
    omega
  have hm3 := lor_range (zlor (zlor slack (slack / 2)) (zlor slack (slack / 2) / 4))
    (zlor (zlor slack (slack / 2)) (zlor slack (slack / 2) / 4) / 16) 64 ⟨hm2.1, hm2.2⟩ ⟨hs16.1, hs16.2⟩
  exact ⟨hm3.1, hm3.2⟩

theorem enframe_off_255 (slack off0 : Int) (Hs : 0 ≤ slack)
    (Ho : 0 ≤ off0 ∧ off0 < 256) : enframe_off slack off0 ≤ 255 := by
  by_cases hle : off0 ≤ slack
  · unfold enframe_off
    rw [ite_eq_left hle]
    omega
  · have := (enframe_off_le slack off0 Hs Ho).2
    omega

theorem div_range64 (a d : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hd : 0 < d) :
    0 ≤ a / d ∧ a / d < 2 ^ 64 := by
  have h1 : 0 ≤ a / d := Int.ediv_nonneg Ha.1 (Int.le_of_lt Hd)
  have h2 : a / d ≤ a := Int.ediv_le_self d Ha.1
  omega

theorem div_le_self (a d : Int) (Ha : 0 ≤ a) (Hd : 0 < d) : 0 ≤ a / d ∧ a / d ≤ a :=
  ⟨Int.ediv_nonneg Ha (Int.le_of_lt Hd), Int.ediv_le_self d Ha⟩

theorem u8_lit (z : Int) (Hz : 0 ≤ z ∧ z < 256) : ((BitVec.ofInt 8 z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt]
  have h8 : ((2 ^ 8 : Nat) : Int) = 256 := by decide
  rw [h8, Int.emod_eq_of_lt Hz.1 Hz.2, Int.toNat_of_nonneg Hz.1]

theorem v_andi_255 (x : word) : v_andi x 255 = BitVec.ofInt 64 ((x.toNat : Int) % 256) := by
  have hw : bv_wrap 64 255 = 255 := by
    unfold bv_wrap
    rw [two_pow64_cast, Int.emod_eq_of_lt (by omega) (by omega)]
  unfold v_andi
  rw [hw, land_255 ((x.toNat : Int)) (Int.natCast_nonneg _)]

theorem v_andi_31 (x : word) : v_andi x 31 = BitVec.ofInt 64 ((x.toNat : Int) % 32) := by
  have hw : bv_wrap 64 31 = 31 := by
    unfold bv_wrap
    rw [two_pow64_cast, Int.emod_eq_of_lt (by omega) (by omega)]
  unfold v_andi
  rw [hw, fld_lastidx ((x.toNat : Int)) (Int.natCast_nonneg _)]

theorem v_not_lit (s : Int) (Hs : 0 ≤ s ∧ s < 2 ^ 64) :
    v_xori (BitVec.ofInt 64 s) (-1) = BitVec.ofInt 64 (2 ^ 64 - 1 - s) := by
  have h := u_not s Hs
  rw [← h]
  rw [show ((v_xori (BitVec.ofInt 64 s) (-1)).toNat : Int)
        = (((v_xori (BitVec.ofInt 64 s) (-1)).toNat : Nat) : Int) from rfl]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- [z_lor] is commutative (it is `Nat`'s `|||`). -/
theorem z_lor_comm (a b : Int) : z_lor a b = z_lor b a := by
  unfold z_lor
  rw [Nat.or_comm]

theorem smear_via_regs (S : Int) (HS : 0 ≤ S) :
    let m1 := z_lor S (S / 2)
    let m2 := z_lor (m1 / 4) m1
    z_lor (m2 / 16) m2 = smear S := by
  intro HS
  simp only []
  unfold smear
  simp only []
  rw [z_lor_comm (z_lor S (S / 2) / 4),
    z_lor_comm (z_lor (z_lor S (S / 2)) (z_lor S (S / 2) / 4) / 16)]

/-! ### The instruction idioms of the enframe summary -/

/-- `xor` with all-ones within 64 bits is `ofInt (-1)`. -/
theorem neg_one_ofInt : BitVec.ofInt 64 (-1) = BitVec.ofInt 64 (2 ^ 64 - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, two_pow64_cast]
  rw [show (-1 : Int) = (2 ^ 64 - 1) + 2 ^ 64 * (-1) from by omega,
    Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (a := 2 ^ 64 - 1) (b := 2 ^ 64) (by omega) (by omega)]

/-- An all-ones mask keeps every bit: `zland (2^64-1) K = K`. -/
theorem ones_zland (K : Int) (HK : 0 ≤ K ∧ K < 2 ^ 64) : zland (2 ^ 64 - 1) K = K := by
  unfold zland
  rw [show ((2 ^ 64 - 1 : Int)).toNat = 2 ^ 64 - 1 from by decide,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (by omega), Int.toNat_of_nonneg HK.1]

theorem neg_mask (b : Bool) (K : Int) (HK : 0 ≤ K ∧ K < 2 ^ 64) :
    v_and (v_subw (BitVec.ofInt 64 0) (BitVec.ofInt 64 (if b then 1 else 0)))
      (BitVec.ofInt 64 K) = BitVec.ofInt 64 (if b then K else 0) := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [v_subw_lit 0 0 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)]
    rw [show (0 : Int) - 0 = 0 from by omega, v_and_lit 0 K ⟨by omega, by omega⟩ HK]
    congr 1
    unfold zland
    rw [show (Int.toNat 0 : Nat) = 0 from by decide, Nat.zero_and]
    rfl
  · simp only [Bool.true_eq_false, ite_true]
    rw [v_subw_lit 0 1 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega),
      show (0 : Int) - 1 = -1 from by omega, neg_one_ofInt, v_and_lit (2 ^ 64 - 1) K ⟨by omega, by omega⟩ HK, ones_zland K HK]

theorem addw_mask (b : Bool) (S om : Int) (HS : 0 ≤ S ∧ S < 2 ^ 64)
    (Hom : 0 ≤ om ∧ om < 2 ^ 31) (Hb : b = true → S < om) :
    v_addw (BitVec.ofInt 64 (if b then 2 ^ 64 - 1 - S else 0)) (BitVec.ofInt 64 om)
      = BitVec.ofInt 64 (if b then om - S - 1 else om) := by
  have h32 : (2 : Int) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
  have Hom64 : 0 ≤ om ∧ om < 2 ^ 64 := ⟨Hom.1, by omega⟩
  have Homr : -2 ^ 31 ≤ om ∧ om < 2 ^ 31 := ⟨by omega, Hom.2⟩
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    have hx : ((BitVec.ofInt 64 0).toNat : Int) = 0 :=
      AgentLib.u64_lit 0 ⟨by omega, by omega⟩
    have hy : ((BitVec.ofInt 64 om).toNat : Int) = om := AgentLib.u64_lit om Hom64
    exact v_addw_small _ _ om Homr ⟨0, by rw [hx, hy]; omega⟩
  · simp only [Bool.true_eq_false, ite_true]
    have hb : S < om := Hb rfl
    have hx : ((BitVec.ofInt 64 (2 ^ 64 - 1 - S)).toNat : Int) = 2 ^ 64 - 1 - S :=
      AgentLib.u64_lit _ ⟨by omega, by omega⟩
    have hy : ((BitVec.ofInt 64 om).toNat : Int) = om := AgentLib.u64_lit om Hom64
    exact v_addw_small _ _ (om - S - 1) (by omega) ⟨2 ^ 32, by rw [hx, hy, h32]; omega⟩

theorem v_add_neg (e r : Int) (Hr : 0 ≤ r ∧ r ≤ e) (He : e < 2 ^ 64) :
    v_add (BitVec.ofInt 64 e) (BitVec.ofInt 64 (0 - r)) = BitVec.ofInt 64 (e - r) := by
  have he : 0 ≤ e := by omega
  have hmod : (0 - r) % (2 ^ 64) = (2 ^ 64 - r) % (2 ^ 64) := by
    rw [show (0 : Int) - r = (2 ^ 64 - r) + 2 ^ 64 * (-1) from by omega,
      Int.add_mul_emod_self_left]
  have hx : ((BitVec.ofInt 64 e).toNat : Int) = e := AgentLib.u64_lit e ⟨he, He⟩
  have hy : ((BitVec.ofInt 64 (0 - r)).toNat : Int) = (2 ^ 64 - r) % (2 ^ 64) := by
    rw [BitVec.toNat_ofInt, AgentLib.two_pow64_cast, hmod]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have harg : (e + (2 ^ 64 - r) % (2 ^ 64)) % (2 ^ 64) = (e - r) % (2 ^ 64) := by
    rw [Int.add_comm e ((2 ^ 64 - r) % (2 ^ 64)), Int.emod_add_emod,
      show (2 ^ 64 - r) + e = (e - r) + 2 ^ 64 * 1 from by omega,
      Int.add_mul_emod_self_left]
  unfold v_add
  rw [hx, hy]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, AgentLib.two_pow64_cast, harg]
  try rw [BitVec.toNat_ofInt, AgentLib.two_pow64_cast]

theorem c_lts_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 63) (Hb : 0 ≤ b ∧ b < 2 ^ 63) :
    c_lts (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a < b) := by
  unfold c_lts bv_lts
  rw [AgentLib.bv_signed_small a Ha, AgentLib.bv_signed_small b Hb]

end LinuxSem.Common.RefEnframeArith
