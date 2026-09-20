import VCDimConvexBound.AffineSliceInterval
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Rectangular constraint matrices with nonsingular column deletions

A k by k+1 matrix with a nonsingular maximal minor is onto and has a
one-dimensional kernel. Its fibers are actual affine lines. If every column
deletion is nonsingular, every nonzero kernel vector has all coordinates
nonzero. These are determinant criteria, not new unproved core assumptions.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

/-- Delete column p, retaining the natural order on the remaining columns. -/
def sliceDeleteColumn {k : ℕ} (B : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (p : Fin (k + 1)) : Matrix (Fin k) (Fin k) ℝ := B.submatrix id p.succAbove

/-- Split the matrix-vector product into the deleted column and the rest. -/
theorem sliceDeleteColumn_mulVec {k : ℕ} (B : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (p : Fin (k + 1)) (x : Fin (k + 1) → ℝ) :
    B *ᵥ x = (fun r => B r p * x p) +
      sliceDeleteColumn B p *ᵥ (fun j => x (p.succAbove j)) := by
  funext r
  exact Fin.sum_univ_succAbove (fun j => B r j * x j) p

/-- Insert a zero in the omitted coordinate. -/
theorem sliceDeleteColumn_insert_zero {k : ℕ}
    (B : Matrix (Fin k) (Fin (k + 1)) ℝ) (p : Fin (k + 1)) (x : Fin k → ℝ) :
    B *ᵥ Fin.insertNth p 0 x = sliceDeleteColumn B p *ᵥ x := by
  rw [sliceDeleteColumn_mulVec B p]
  simp
  rfl

/-- A nonsingular column deletion supplies every right-hand side. -/
theorem sliceMatrix_surjective {k : ℕ} (B : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (p : Fin (k + 1)) (hdet : (sliceDeleteColumn B p).det ≠ 0) :
    Function.Surjective B.mulVecLin := by
  have hu : IsUnit (sliceDeleteColumn B p) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  intro b
  obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu b
  exact ⟨Fin.insertNth p 0 x, (sliceDeleteColumn_insert_zero B p x).trans hx⟩

/-- A kernel vector cannot vanish in the deleted coordinate unless it is zero. -/
theorem sliceMatrix_kernel_eq_zero_of_coord_zero {k : ℕ}
    (B : Matrix (Fin k) (Fin (k + 1)) ℝ) (p : Fin (k + 1))
    (hdet : (sliceDeleteColumn B p).det ≠ 0) (w : Fin (k + 1) → ℝ)
    (hw : B *ᵥ w = 0) (hp : w p = 0) : w = 0 := by
  have hu : IsUnit (sliceDeleteColumn B p) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hrest : sliceDeleteColumn B p *ᵥ (fun j => w (p.succAbove j)) = 0 := by
    funext r
    have h := congrFun ((sliceDeleteColumn_mulVec B p w).symm.trans hw) r
    simpa [hp] using h
  have hz : (fun j => w (p.succAbove j)) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (hrest.trans (Matrix.mulVec_zero _).symm)
  funext i
  refine Fin.succAboveCases p ?_ (fun j => ?_) i
  · exact hp
  · exact congrFun hz j

/-- All maximal deletion minors nonzero implies no zero coordinate in a kernel direction. -/
theorem sliceMatrix_kernel_all_ne_zero {k : ℕ}
    (B : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (hdet : ∀ p, (sliceDeleteColumn B p).det ≠ 0)
    (w : Fin (k + 1) → ℝ) (hw : B *ᵥ w = 0) (hne : w ≠ 0) :
    ∀ p, w p ≠ 0 := by
  intro p hp
  exact hne (sliceMatrix_kernel_eq_zero_of_coord_zero B p (hdet p) w hw hp)

/-- Rank-nullity for one more column than rows. -/
theorem sliceMatrix_finrank_ker {k : ℕ} (B : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (p : Fin (k + 1)) (hdet : (sliceDeleteColumn B p).det ≠ 0) :
    Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
  have hr := LinearMap.range_eq_top.mpr (sliceMatrix_surjective B p hdet)
  have h := B.mulVecLin.finrank_range_add_finrank_ker
  rw [hr] at h
  simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h
  omega

/-- A fiber of a linear map with one-dimensional kernel is an affine line. -/
theorem sliceMatrix_fiber_iff {k : ℕ} (B : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (hker : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1)
    (a w : Fin (k + 1) → ℝ) (hw : B *ᵥ w = 0) (hne : w ≠ 0)
    (x : Fin (k + 1) → ℝ) :
    B *ᵥ x = B *ᵥ a ↔ ∃ t : ℝ, x = sliceCoeff a w t := by
  constructor
  · intro hx
    have hdiff : B *ᵥ (x - a) = 0 := by rw [Matrix.mulVec_sub, hx, sub_self]
    let w' : LinearMap.ker B.mulVecLin := ⟨w, hw⟩
    have hw' : w' ≠ 0 := fun h => hne (congrArg Subtype.val h)
    obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hker hw'
      (⟨x - a, hdiff⟩ : LinearMap.ker B.mulVecLin)
    refine ⟨t, ?_⟩
    have hv := congrArg Subtype.val ht
    funext i
    have hi := congrFun hv i
    change t * w i = x i - a i at hi
    change x i = a i + t * w i
    linarith
  · rintro ⟨t, rfl⟩
    change B.mulVecLin (a + t • w) = B.mulVecLin a
    rw [map_add, map_smul]
    change B *ᵥ a + t • (B *ᵥ w) = B *ᵥ a
    rw [hw, smul_zero, add_zero]

/-- All deletion minors nonzero yield a mass-independent affine parameterization
of every fiber, with nonzero slope in every coordinate. -/
theorem exists_sliceMatrix_line {k : ℕ} (B : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (hdet : ∀ p, (sliceDeleteColumn B p).det ≠ 0) (b : Fin k → ℝ) :
    ∃ a w : Fin (k + 1) → ℝ,
      B *ᵥ a = b ∧ B *ᵥ w = 0 ∧ w ≠ 0 ∧ (∀ i, w i ≠ 0) ∧
      (∀ x, B *ᵥ x = b ↔ ∃ t : ℝ, x = sliceCoeff a w t) := by
  have hker := sliceMatrix_finrank_ker B 0 (hdet 0)
  have hbot : LinearMap.ker B.mulVecLin ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hker
    omega
  obtain ⟨w, hw, hne⟩ := (LinearMap.ker B.mulVecLin).ne_bot_iff.mp hbot
  obtain ⟨a, ha⟩ := sliceMatrix_surjective B 0 (hdet 0) b
  refine ⟨a, w, ha, hw, hne, sliceMatrix_kernel_all_ne_zero B hdet w hw hne, ?_⟩
  intro x
  rw [← ha]
  exact sliceMatrix_fiber_iff B hker a w hw hne x

end VCDimConvexBound
