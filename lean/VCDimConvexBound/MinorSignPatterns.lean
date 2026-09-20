import VCDimConvexBound.Minors
import VCDimConvexBound.WarrenApplication

/-!
# Counting all-minor sign patterns, conditional on Warren

This connects the polynomial encoding of additive arrays with the proved
ternary-to-strict reduction. The geometric assertion that minor signs determine
convex-hull membership is proved separately in `MinorHullRecovery`.
Warren itself is still unproved.
-/

namespace VCDimConvexBound

/-- All ternary sign vectors of the polynomial minor family. -/
noncomputable def minorSignPatterns (D m : ℕ) : Finset (MinorIndex D m → Fin 3) :=
  ternaryPatterns (fun j x => MvPolynomial.eval x (minorPolynomial j))

/-- Substitute the minor degree, number of variables, and index-count bound into Warren. -/
theorem card_minorSignPatterns_le_of_warren (hW : WarrenStrictBound)
    (D m : ℕ) (hD : 2 ≤ D) (hm : D ^ 2 ≤ m) :
    ((minorSignPatterns D m).card : ℝ) ≤
      (8 * Real.exp 1 * D * (2 ^ (D + 1) * ((m : ℝ) ^ D) ^ (D + 1)) /
        (D ^ 2 * m + 1)) ^ (D ^ 2 * m + 1) := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have h := card_ternaryPatterns_le_of_warren hW D (by omega)
    (show Fintype.card (ArrayVar D m) + 1 ≤ 2 * Fintype.card (MinorIndex D m) by
      rw [card_arrayVar]
      exact minor_warren_size_condition D m hD hm)
    (minorPolynomial (D := D) (m := m)) totalDegree_minorPolynomial_le
  simp only [card_arrayVar] at h
  change ((minorSignPatterns D m).card : ℝ) ≤ _ at h
  have hcount : (Fintype.card (MinorIndex D m) : ℝ) ≤
      2 ^ (D + 1) * ((m : ℝ) ^ D) ^ (D + 1) := by
    exact_mod_cast card_minorIndex_le D m hm0
  push_cast at h
  exact h.trans (by gcongr)

/-- The side length already chosen in P3 meets the elementary Warren size condition. -/
theorem sq_le_explicit_side (D : ℕ) (hD : 2 ≤ D) :
    D ^ 2 ≤ 2 ^ (8 * (D + 1) ^ (D - 1)) := by
  have hbase : D ≤ 2 ^ D := (Nat.lt_two_pow_self (n := D)).le
  have hexp : D + 1 ≤ (D + 1) ^ (D - 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < D + 1) (by omega : 1 ≤ D - 1)
  calc
    D ^ 2 ≤ (2 ^ D) ^ 2 := by gcongr
    _ = 2 ^ (D * 2) := (pow_mul 2 D 2).symm
    _ ≤ 2 ^ (8 * (D + 1) ^ (D - 1)) :=
      Nat.pow_le_pow_right (by decide) (by omega)

end VCDimConvexBound
