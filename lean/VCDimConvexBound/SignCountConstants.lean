import VCDimConvexBound.MinorSignPatterns
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary power bounds for the minor sign count

We deliberately overestimate the Warren expression, retaining the original
side length m = 2^(8(D+1)^(D-1)). No logarithms or giant enumerations are needed.
-/

namespace VCDimConvexBound

/-- The elementary exponential budget behind the sign count. -/
theorem explicit_sign_exponent_budget (D : ℕ) (hD : 2 ≤ D) :
    8 * (8 * (D + 1) ^ (D - 1)) * (D + 1) ^ 4 <
      2 ^ (8 * (D + 1) ^ (D - 1)) := by
  let s := (D + 1) ^ (D - 1)
  have hDs : D + 1 ≤ s := by
    simpa [s] using Nat.pow_le_pow_right (by omega : 0 < D + 1) (by omega : 1 ≤ D - 1)
  have hs : 3 ≤ s := by omega
  have hs2 : s ≤ 2 ^ s := (Nat.lt_two_pow_self (n := s)).le
  calc
    8 * (8 * s) * (D + 1) ^ 4 ≤ 64 * s ^ 5 := by
      calc
        _ ≤ 8 * (8 * s) * s ^ 4 := by gcongr
        _ = _ := by ring
    _ ≤ 64 * (2 ^ s) ^ 5 := by gcongr
    _ = 2 ^ (6 + 5 * s) := by
      rw [pow_add, ← pow_mul, Nat.mul_comm s 5]
      norm_num
    _ < 2 ^ (8 * s) := Nat.pow_lt_pow_right (by decide) (by omega)

/-- Replace the real Warren base by a convenient power of two. -/
theorem minor_warren_base_le_two_pow (D L : ℕ) (hL : 8 ≤ L) :
    8 * Real.exp 1 * D * (2 ^ (D + 1) * (((2 ^ L : ℕ) : ℝ) ^ D) ^ (D + 1)) /
      (D ^ 2 * (2 ^ L : ℕ) + 1) ≤ (2 : ℝ) ^ (2 * L * (D + 1) ^ 2) := by
  have hD2 : (D : ℝ) ≤ (2 : ℝ) ^ D := by
    exact_mod_cast (Nat.lt_two_pow_self (n := D)).le
  have he : Real.exp 1 ≤ (4 : ℝ) := Real.exp_one_lt_three.le.trans (by norm_num)
  have hexp : 6 + 2 * D + L * D * (D + 1) ≤ 2 * L * (D + 1) ^ 2 := by
    nlinarith
  calc
    _ ≤ 8 * Real.exp 1 * D *
        (2 ^ (D + 1) * (((2 ^ L : ℕ) : ℝ) ^ D) ^ (D + 1)) :=
      div_le_self (by positivity) (le_add_of_nonneg_left (by positivity))
    _ ≤ 8 * 4 * (2 : ℝ) ^ D *
        (2 ^ (D + 1) * (((2 ^ L : ℕ) : ℝ) ^ D) ^ (D + 1)) := by gcongr
    _ = (2 : ℝ) ^ (6 + 2 * D + L * D * (D + 1)) := by
      push_cast
      rw [show 8 * (4 : ℝ) = 2 ^ 5 by norm_num]
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp

/-- A natural exponent upper bound for the sign-pattern count, conditional on Warren. -/
theorem card_minorSignPatterns_le_two_pow_of_warren (hW : WarrenStrictBound)
    (D L : ℕ) (hD : 2 ≤ D) (hL : 8 ≤ L) (hm : D ^ 2 ≤ 2 ^ L) :
    (minorSignPatterns D (2 ^ L)).card ≤ 2 ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
  have hw := card_minorSignPatterns_le_of_warren hW D (2 ^ L) hD hm
  have hb := minor_warren_base_le_two_pow D L hL
  have hp : D ^ 2 * 2 ^ L + 1 ≤ 2 * (D + 1) ^ 2 * 2 ^ L := by
    have hm0 : 0 < (2 : ℕ) ^ L := by positivity
    nlinarith [Nat.pow_le_pow_left (show D ≤ D + 1 by omega) 2]
  have hexp : (2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 1) ≤
      4 * L * (D + 1) ^ 4 * 2 ^ L := by
    calc
      _ ≤ (2 * L * (D + 1) ^ 2) * (2 * (D + 1) ^ 2 * 2 ^ L) := by gcongr
      _ = _ := by ring
  have hr : ((minorSignPatterns D (2 ^ L)).card : ℝ) ≤
      (2 : ℝ) ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
    calc
      _ ≤ _ := hw
      _ ≤ ((2 : ℝ) ^ (2 * L * (D + 1) ^ 2)) ^ (D ^ 2 * 2 ^ L + 1) := by
        gcongr
      _ = (2 : ℝ) ^ ((2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 1)) :=
        (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp
  exact_mod_cast hr

/-- P7: the sign factor uses strictly less than half the bit budget. -/
theorem card_minorSignPatterns_explicit_sq_lt_of_warren (hW : WarrenStrictBound)
    (D : ℕ) (hD : 2 ≤ D) :
    (minorSignPatterns D (2 ^ (8 * (D + 1) ^ (D - 1)))).card ^ 2 <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  let L := 8 * (D + 1) ^ (D - 1)
  let m := 2 ^ L
  have hL : 8 ≤ L := by
    have h : 0 < (D + 1) ^ (D - 1) := by positivity
    dsimp [L]; omega
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hb : 8 * L * (D + 1) ^ 4 < m := explicit_sign_exponent_budget D hD
  have hmD : m ^ 2 ≤ m ^ D := Nat.pow_le_pow_right hm0 hD
  have hexp : (4 * L * (D + 1) ^ 4 * m) * 2 < m ^ D := by
    calc
      _ = (8 * L * (D + 1) ^ 4) * m := by ring
      _ < m * m := Nat.mul_lt_mul_of_pos_right hb hm0
      _ ≤ m ^ D := by simpa [pow_two] using hmD
  have ht := card_minorSignPatterns_le_two_pow_of_warren hW D L hD hL
    (sq_le_explicit_side D hD)
  calc
    _ ≤ (2 ^ (4 * L * (D + 1) ^ 4 * m)) ^ 2 := Nat.pow_le_pow_left ht 2
    _ = 2 ^ ((4 * L * (D + 1) ^ 4 * m) * 2) := (pow_mul _ _ _).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) hexp

end VCDimConvexBound
