import VCDimConvexBound.SparseSubsetCount
import VCDimConvexBound.SignCountConstants
import VCDimConvexBound.Shattering

/-!
# The explicit VC bound, conditional only on Sanyal and Warren

P7 supplies the previously assumed label-count estimate. These final theorems
still take the two unproved core propositions as explicit arguments; they do
not constitute an unconditional solution of the Formal Conjectures problem.
-/

namespace VCDimConvexBound

/-- Two factors each below the square-root budget have product below the total budget. -/
theorem mul_lt_of_sq_lt {a b c : ℕ} (ha : a ^ 2 < c) (hb : b ^ 2 < c) :
    a * b < c := by
  have hsq : (a * b) ^ 2 < c ^ 2 := by
    rw [mul_pow, pow_two c]
    calc
      a ^ 2 * b ^ 2 ≤ c * b ^ 2 := Nat.mul_le_mul_right _ ha.le
      _ < c * c := Nat.mul_lt_mul_of_pos_left hb (by omega)
  nlinarith

/-- P7, including all constants and every D≥2, conditional on the two core inputs. -/
theorem card_convexLabels_lt_of_sanyal_warren (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D) (hW : WarrenStrictBound) :
    (convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))).card <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  exact (card_convexLabels_le_signs_mul_sparse_of_sanyal D hD hS).trans_lt
    (mul_lt_of_sq_lt (card_minorSignPatterns_explicit_sq_lt_of_warren hW D hD)
      (card_sparseSubsets_explicit_sq_lt D hD))

/-- The original explicit bound now requires only Sanyal and Warren, with no hcount. -/
theorem explicit_bound_of_sanyal_warren (n : ℕ) (hn : 1 ≤ n)
    (hS : SanyalBoxObstruction (n + 1)) (hW : WarrenStrictBound)
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) := by
  apply explicit_bound_of_label_count n _ C hC
  simpa [Nat.add_assoc] using
    card_convexLabels_lt_of_sanyal_warren (n + 1) (by omega) hS hW

/-- The FC existence statement with exactly the two unproved core inputs remaining. -/
theorem exists_bound_of_sanyal_warren
    (hS : ∀ D : ℕ, 2 ≤ D → SanyalBoxObstruction D) (hW : WarrenStrictBound)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d := by
  exact ⟨bound n, fun C hC => explicit_bound_of_sanyal_warren n hn
    (hS (n + 1) (by omega)) hW C hC⟩

end VCDimConvexBound
