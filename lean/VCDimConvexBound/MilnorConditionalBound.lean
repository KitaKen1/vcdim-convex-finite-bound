import VCDimConvexBound.CoarseSignCount
import VCDimConvexBound.ConditionalBound

/-!
# The original explicit VC bound using a coarse hypersurface input

This is an alternative conditional proof, not a proof of either remaining
core. Sanyal and the hypersurface component bound are explicit arguments.
Warren's theorem is not an argument of these declarations.
-/

namespace VCDimConvexBound

theorem card_convexLabels_lt_of_sanyal_hypersurface (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D) (hM : HypersurfaceComponentBound) :
    (convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))).card <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  exact (card_convexLabels_le_signs_mul_sparse_of_sanyal D hD hS).trans_lt
    (mul_lt_of_sq_lt (card_minorSignPatterns_explicit_sq_lt_of_hypersurface hM D hD)
      (card_sparseSubsets_explicit_sq_lt D hD))

/-- The same explicit bound, assuming Sanyal and a coarse component estimate. -/
theorem explicit_bound_of_sanyal_hypersurface (n : ℕ) (hn : 1 ≤ n)
    (hS : SanyalBoxObstruction (n + 1)) (hM : HypersurfaceComponentBound)
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) := by
  apply explicit_bound_of_label_count n _ C hC
  simpa [Nat.add_assoc] using
    card_convexLabels_lt_of_sanyal_hypersurface (n + 1) (by omega) hS hM

/-- The FC existence conclusion with the new route's two obligations still explicit. -/
theorem exists_bound_of_sanyal_hypersurface
    (hS : ∀ D : ℕ, 2 ≤ D → SanyalBoxObstruction D) (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d := by
  exact ⟨bound n, fun C hC => explicit_bound_of_sanyal_hypersurface n hn
    (hS (n + 1) (by omega)) hM C hC⟩

end VCDimConvexBound
