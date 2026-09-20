import VCDimConvexBound.SanyalSeparation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Arbitrarily small simultaneous perturbations to simplices

Move the non-base vertices along the coordinate basis. The difference matrix
is A+tI, whose determinant is a nonzero monic polynomial in t. Only finitely
many t are forbidden, even for finitely many families. Convex independence of
all sums is open, so a hypothetical counterexample survives this perturbation.
-/

namespace VCDimConvexBound

/-- Rows are the edge vectors from the base point. -/
def simplexDifferenceMatrix {D : ℕ} (q : Fin (D + 1) → Point D) :
    Matrix (Fin D) (Fin D) ℝ := fun j a => q j.succ a - q 0 a

/-- Keep the base point fixed and perturb the other vertices in coordinate directions. -/
def perturbSimplex {D : ℕ} (q : Fin (D + 1) → Point D) (t : ℝ) :
    Fin (D + 1) → Point D :=
  Fin.cons (q 0) (fun j => q j.succ + t • Pi.single j 1)

@[simp] theorem perturbSimplex_zero {D : ℕ} (q : Fin (D + 1) → Point D) :
    perturbSimplex q 0 = q := by
  ext i a
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [perturbSimplex]

theorem continuous_perturbSimplex {D : ℕ} (q : Fin (D + 1) → Point D) :
    Continuous (perturbSimplex q) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [perturbSimplex, Fin.cons_zero,
    Fin.cons_succ] <;> fun_prop

/-- Nonzero determinant of the difference matrix certifies affine independence. -/
theorem affineIndependent_of_difference_det_ne_zero {D : ℕ}
    (q : Fin (D + 1) → Point D) (h : (simplexDifferenceMatrix q).det ≠ 0) :
    AffineIndependent ℝ q := by
  have hl : LinearIndependent ℝ (simplexDifferenceMatrix q).row :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
  rw [affineIndependent_iff_linearIndependent_vsub ℝ q 0]
  apply (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (D + 1)))).mp
  simpa [simplexDifferenceMatrix, Matrix.row, Function.comp_def, finSuccAboveEquiv_apply]
    using! hl

theorem simplexDifferenceMatrix_perturb {D : ℕ} (q : Fin (D + 1) → Point D)
    (t : ℝ) :
    simplexDifferenceMatrix (perturbSimplex q t) =
      Matrix.scalar (Fin D) t - (-simplexDifferenceMatrix q) := by
  ext j a
  by_cases h : j = a
  · subst a
    simp [simplexDifferenceMatrix, perturbSimplex, Matrix.scalar, Matrix.diagonal]
    ring
  · simp [simplexDifferenceMatrix, perturbSimplex, Matrix.scalar, Matrix.diagonal,
      h, Ne.symm h]

/-- The only forbidden perturbations are roots of one characteristic polynomial. -/
theorem affineIndependent_perturbSimplex_of_not_isRoot {D : ℕ}
    (q : Fin (D + 1) → Point D) (t : ℝ)
    (ht : ¬ (-simplexDifferenceMatrix q).charpoly.IsRoot t) :
    AffineIndependent ℝ (perturbSimplex q t) := by
  apply affineIndependent_of_difference_det_ne_zero
  simpa only [Polynomial.IsRoot, Matrix.eval_charpoly, simplexDifferenceMatrix_perturb] using ht

/-- Any open neighbourhood of an array contains one whose every family is a simplex. -/
theorem exists_affineIndependent_families_mem_open {r D : ℕ}
    (z : Fin r → Fin (D + 1) → Point D)
    (U : Set (Fin r → Fin (D + 1) → Point D)) (hU : IsOpen U) (hz : z ∈ U) :
    ∃ w ∈ U, ∀ k, AffineIndependent ℝ (w k) := by
  classical
  let bad : Finset ℝ := Finset.univ.biUnion fun k : Fin r =>
    (-simplexDifferenceMatrix (z k)).charpoly.roots.toFinset
  have hd : Dense ((bad : Set ℝ)ᶜ) := by
    simpa only [Set.compl_eq_univ_sdiff] using (dense_univ : Dense (Set.univ : Set ℝ)).sdiff_finset bad
  let path : ℝ → Fin r → Fin (D + 1) → Point D := fun t k => perturbSimplex (z k) t
  have hc : Continuous path := continuous_pi fun k => continuous_perturbSimplex (z k)
  have hzero : path 0 ∈ U := by simpa [path] using hz
  obtain ⟨t, htU, htbad⟩ := hd.inter_open_nonempty (path ⁻¹' U) (hU.preimage hc) ⟨0, hzero⟩
  refine ⟨path t, htU, fun k => ?_⟩
  apply affineIndependent_perturbSimplex_of_not_isRoot
  intro hr
  apply htbad
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_univ k, ?_⟩
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots
    (Matrix.charpoly_monic _).ne_zero).mpr hr)

/-- Degenerate counterexamples could be perturbed into full-dimensional simplex counterexamples. -/
theorem exists_simplex_counterexample_of_convexIndependent_gridSum {r D : ℕ}
    (z : Fin r → Fin (D + 1) → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    ∃ w : Fin r → Fin (D + 1) → Point D,
      (∀ k, AffineIndependent ℝ (w k)) ∧ ConvexIndependent ℝ (gridSum w) := by
  obtain ⟨w, hw, ha⟩ := exists_affineIndependent_families_mem_open z _
    (isOpen_convexIndependent_gridSum r (D + 1) D) hz
  exact ⟨w, ha, hw⟩

/-- Sanyal's remaining input can be restricted to families of genuine simplices. -/
theorem sanyalBoxObstruction_iff_simplex_obstruction (D : ℕ) :
    SanyalBoxObstruction D ↔
      ∀ z : Fin D → Fin (D + 1) → Point D,
        (∀ k, AffineIndependent ℝ (z k)) → ¬ ConvexIndependent ℝ (gridSum z) := by
  constructor
  · intro h z _
    exact h z
  · intro h z hz
    obtain ⟨w, ha, hw⟩ := exists_simplex_counterexample_of_convexIndependent_gridSum z hz
    exact h w ha hw

end VCDimConvexBound
