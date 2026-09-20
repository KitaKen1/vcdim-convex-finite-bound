import VCDimConvexBound.DirectSignCount
import VCDimConvexBound.HexagonConeExistence

/-!
# The explicit VC bound without unproved geometric or sign-count inputs

The direct polynomial sign count supplies the existing numerical budget.
The proved Sanyal obstruction and label-count reduction then give the
original bound and the Formal Conjectures existence statement.
-/

namespace VCDimConvexBound

/-- All minor sign patterns obey the coarse budget, unconditionally. -/
theorem card_minorSignPatterns_le_direct (D m : ℕ) (hD : 1 ≤ D) (hm : 0 < m) :
    (minorSignPatterns D m).card ≤
      (4 * D * (2 ^ (D + 1) * (m ^ D) ^ (D + 1)) + 2) ^ (D ^ 2 * m + 2) := by
  have h := card_ternaryPatterns_le_coarse_direct D hD
    (minorPolynomial (D := D) (m := m)) totalDegree_minorPolynomial_le
  simp only [card_arrayVar] at h
  change (minorSignPatterns D m).card ≤ _ at h
  exact h.trans (by gcongr; exact card_minorIndex_le D m hm)

/-- The previously established numerical estimates apply to the direct sign count. -/
theorem card_minorSignPatterns_le_two_pow_direct (D L : ℕ) (hD : 1 ≤ D) (hL : 8 ≤ L) :
    (minorSignPatterns D (2 ^ L)).card ≤ 2 ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
  have hm : 0 < (2 : ℕ) ^ L := by positivity
  have hp : D ^ 2 * 2 ^ L + 2 ≤ 2 * (D + 1) ^ 2 * 2 ^ L := by
    calc
      _ ≤ (D ^ 2 + 2) * 2 ^ L := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith : D ^ 2 + 2 ≤ 2 * (D + 1) ^ 2)
  have he : (2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2) ≤
      4 * L * (D + 1) ^ 4 * 2 ^ L := by
    calc
      _ ≤ (2 * L * (D + 1) ^ 2) * (2 * (D + 1) ^ 2 * 2 ^ L) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ _ := card_minorSignPatterns_le_direct D (2 ^ L) hD hm
    _ ≤ (2 ^ (2 * L * (D + 1) ^ 2)) ^ (D ^ 2 * 2 ^ L + 2) :=
      Nat.pow_le_pow_left (minor_hypersurface_base_le_two_pow D L hD hL) _
    _ = 2 ^ ((2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

/-- At the original explicit side length, the square sign count is strictly below 2^M. -/
theorem card_minorSignPatterns_explicit_sq_lt_direct (D : ℕ) (hD : 2 ≤ D) :
    (minorSignPatterns D (2 ^ (8 * (D + 1) ^ (D - 1)))).card ^ 2 <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  let L := 8 * (D + 1) ^ (D - 1)
  let m := 2 ^ L
  have hL : 8 ≤ L := by
    have h : 0 < (D + 1) ^ (D - 1) := by positivity
    dsimp [L]
    omega
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hb : 8 * L * (D + 1) ^ 4 < m := explicit_sign_exponent_budget D hD
  have hmD : m ^ 2 ≤ m ^ D := Nat.pow_le_pow_right hm0 hD
  have he : (4 * L * (D + 1) ^ 4 * m) * 2 < m ^ D := by
    calc
      _ = (8 * L * (D + 1) ^ 4) * m := by ring
      _ < m * m := Nat.mul_lt_mul_of_pos_right hb hm0
      _ ≤ m ^ D := by simpa [pow_two] using hmD
  have ht := card_minorSignPatterns_le_two_pow_direct D L (by omega) hL
  calc
    _ ≤ (2 ^ (4 * L * (D + 1) ^ 4 * m)) ^ 2 := Nat.pow_le_pow_left ht 2
    _ = 2 ^ ((4 * L * (D + 1) ^ 4 * m) * 2) := (pow_mul _ _ _).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) he

/-- Fewer than all labels are realized at the original explicit side length. -/
theorem card_convexLabels_lt_explicit (D : ℕ) (hD : 2 ≤ D) :
    (convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))).card <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  exact (card_convexLabels_le_signs_mul_sparse_of_sanyal D hD
    (sanyalBoxObstruction D hD)).trans_lt
    (mul_lt_of_sq_lt (card_minorSignPatterns_explicit_sq_lt_direct D hD)
      (card_sparseSubsets_explicit_sq_lt D hD))

/-- Every convex set has additive VC_n dimension at most 2^(8*(n+2)^n)-1 for n≥1. -/
theorem explicit_bound (n : ℕ) (hn : 1 ≤ n)
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) := by
  apply explicit_bound_of_label_count n _ C hC
  simpa [Nat.add_assoc] using card_convexLabels_lt_explicit (n + 1) (by omega)

/-- The Formal Conjectures uniform finite-bound existence statement, for every n≥1. -/
theorem exists_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d :=
  ⟨bound n, fun C hC => explicit_bound n hn C hC⟩

end VCDimConvexBound
