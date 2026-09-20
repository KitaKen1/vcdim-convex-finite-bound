import VCDimConvexBound.SimplexPerturbation
import VCDimConvexBound.ConvexCertificates

/-!
# A finite linear certificate for a lost vertex of the Minkowski sum

At a chosen corner, take all edges obtained by changing exactly one summand.
The sum fails to have a strict supporting functional exactly when these edge
vectors admit nonnegative weights summing to one and with weighted sum zero.
The unresolved Sanyal core is reduced to producing such a corner for simplices.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Finite strict separation from zero, including the empty family. -/
theorem zero_mem_convexHull_iff_no_strict_separator {ι : Type*} [Fintype ι] {D : ℕ}
    (q : ι → Point D) :
    (0 : Point D) ∈ convexHull ℝ (Set.range q) ↔
      ¬ ∃ f : Point D →L[ℝ] ℝ, ∀ j, f (q j) < 0 := by
  constructor
  · rintro hzero ⟨f, hf⟩
    have hs : convexHull ℝ (Set.range q) ⊆ {x | f x < 0} := by
      apply convexHull_min _ (convex_halfSpace_lt ⟨f.map_add, f.map_smul⟩ _)
      rintro _ ⟨j, rfl⟩
      exact hf j
    have h : f 0 < 0 := hs hzero
    simp at h
  · intro h
    by_contra hzero
    obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) ((Set.finite_range q).isClosed_convexHull ℝ) hzero
    apply h
    exact ⟨f, fun j => by simpa using (hf _ (subset_convexHull ℝ _ ⟨j, rfl⟩)).trans hu⟩

/-- Edges incident to one vertex of the product of the indexed point sets. -/
abbrev CornerEdge {r m : ℕ} (i : Grid r m) :=
  {e : Fin r × Fin m // e.2 ≠ i e.1}

/-- The image of an incident edge under the summation projection. -/
def cornerVector {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (i : Grid r m) (e : CornerEdge i) : Point D :=
  z e.val.1 e.val.2 - z e.val.1 (i e.val.1)

/-- A normalized nonnegative dependence among the projected incident edges. -/
def BalancedCorner {r m D : ℕ} (z : Fin r → Fin m → Point D) (i : Grid r m) : Prop :=
  ∃ w : CornerEdge i → ℝ, (∀ e, 0 ≤ w e) ∧
    ∑ e, w e = 1 ∧ ∑ e, w e • cornerVector z i e = 0

/-- The coefficient certificate exactly detects failure of a common support at this corner. -/
theorem balancedCorner_iff_no_support {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) :
    BalancedCorner z i ↔ ¬ ∃ f : Point D →L[ℝ] ℝ,
      ∀ k j, j ≠ i k → f (z k j) < f (z k (i k)) := by
  rw [BalancedCorner, ← mem_convexHull_range_iff_weights, zero_mem_convexHull_iff_no_strict_separator]
  apply not_congr
  apply exists_congr
  intro f
  constructor
  · intro h k j hji
    have he := h ⟨(k, j), hji⟩
    simpa only [cornerVector, map_sub, sub_lt_zero] using he
  · intro h e
    simpa only [cornerVector, map_sub, sub_lt_zero] using h e.val.1 e.val.2 e.property

/-- A non-independent array always has a corner carrying a finite balance certificate. -/
theorem not_convexIndependent_gridSum_iff_balancedCorner {r m D : ℕ}
    (z : Fin r → Fin m → Point D) :
    ¬ ConvexIndependent ℝ (gridSum z) ↔ ∃ i, BalancedCorner z i := by
  classical
  simp only [convexIndependent_gridSum_iff_commonStrictMaximizers,
    CommonStrictMaximizers, not_forall, balancedCorner_iff_no_support]

/-- Exact remaining Sanyal obligation after eliminating degeneracies and separation. -/
theorem sanyalBoxObstruction_iff_simplex_balancing (D : ℕ) :
    SanyalBoxObstruction D ↔
      ∀ z : Fin D → Fin (D + 1) → Point D,
        (∀ k, AffineIndependent ℝ (z k)) → ∃ i, BalancedCorner z i := by
  simp only [sanyalBoxObstruction_iff_simplex_obstruction,
    not_convexIndependent_gridSum_iff_balancedCorner]

end VCDimConvexBound
