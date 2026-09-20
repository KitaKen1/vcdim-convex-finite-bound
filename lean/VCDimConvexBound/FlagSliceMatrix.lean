import VCDimConvexBound.SliceConstraintMatrix
import VCDimConvexBound.AffineIntervalParity
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Determinant conditions for a coordinate-flag slice

For r+2 vertices, impose r coordinate equations and coefficient mass one.
The resulting matrix has r+1 rows. Explicit nonzero minors imply the affine
line description, nonzero slopes, no simultaneous coordinate zeros, and the
nondegeneracy of the next height coordinate. No perturbation theorem is
assumed or proved here: the determinant hypotheses remain explicit.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

/-- Prepend a scalar coordinate row to a finite matrix. -/
def flagPrependRow {r n : ℕ} (z : Fin n → ℝ) (X : Matrix (Fin r) (Fin n) ℝ) :
    Matrix (Fin (r + 1)) (Fin n) ℝ := Matrix.of (Fin.cons z (fun i j => X i j))

theorem flagPrependRow_mulVec {r n : ℕ} (z : Fin n → ℝ)
    (X : Matrix (Fin r) (Fin n) ℝ) (x : Fin n → ℝ) :
    flagPrependRow z X *ᵥ x = Fin.cons (∑ i, z i * x i) (X *ᵥ x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [flagPrependRow, Matrix.mulVec, dotProduct]

/-- Coordinate constraints with a first row recording total coefficient mass. -/
def flagConstraintMatrix {r : ℕ} (X : Matrix (Fin r) (Fin (r + 2)) ℝ) :
    Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ := flagPrependRow (fun _ => 1) X

/-- Delete two distinct columns in succession from the r by r+2 coordinate matrix. -/
def flagDoubleMinor {r : ℕ} (X : Matrix (Fin r) (Fin (r + 2)) ℝ)
    (p : Fin (r + 2)) (q : Fin (r + 1)) : Matrix (Fin r) (Fin r) ℝ :=
  X.submatrix id (p.succAbove ∘ q.succAbove)

/-- The concrete finite determinant conditions needed for one simplex slice. -/
structure FlagSliceGeneric {r : ℕ} (X : Matrix (Fin r) (Fin (r + 2)) ℝ)
    (z : Fin (r + 2) → ℝ) : Prop where
  mass_minors : ∀ p, (sliceDeleteColumn (flagConstraintMatrix X) p).det ≠ 0
  coordinate_minors : ∀ p q, (flagDoubleMinor X p q).det ≠ 0
  augmented_height : (flagPrependRow z (flagConstraintMatrix X)).det ≠ 0
  height_minors : ∀ p, (sliceDeleteColumn (flagPrependRow z X) p).det ≠ 0

/-- Deleting a zero coefficient does not change a weighted image. -/
theorem mulVec_delete_zero {ρ : Type*} {k : ℕ}
    (X : Matrix ρ (Fin (k + 1)) ℝ) (x : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) (hp : x p = 0) :
    X.submatrix id p.succAbove *ᵥ (fun j => x (p.succAbove j)) = X *ᵥ x := by
  funext i
  have h := Fin.sum_univ_succAbove (fun j => X i j * x j) p
  simpa [hp, Matrix.mulVec, dotProduct, Matrix.submatrix] using h.symm

/-- Mass and coordinate equations are exactly the rows of the augmented matrix. -/
theorem flagConstraintMatrix_mulVec {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (x : Fin (r + 2) → ℝ) :
    flagConstraintMatrix X *ᵥ x = Fin.cons (∑ i, x i) (X *ᵥ x) := by
  simp [flagConstraintMatrix, flagPrependRow_mulVec]

/-- Matrix equality to the mass-one right-hand side is the original slice system. -/
theorem flagConstraintMatrix_eq_rhs_iff {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (x : Fin (r + 2) → ℝ) :
    flagConstraintMatrix X *ᵥ x = Fin.cons 1 0 ↔ (∑ i, x i) = 1 ∧ X *ᵥ x = 0 := by
  rw [flagConstraintMatrix_mulVec, Fin.cons_inj]

/-- Kernel directions preserve the mass and every coordinate constraint. -/
theorem flagConstraintMatrix_eq_zero_iff {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (w : Fin (r + 2) → ℝ) :
    flagConstraintMatrix X *ᵥ w = 0 ↔ (∑ i, w i) = 0 ∧ X *ᵥ w = 0 := by
  rw [flagConstraintMatrix_mulVec]
  constructor
  · intro h
    exact ⟨congrFun h 0, funext fun j => congrFun h j.succ⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Two zero coefficients force a coordinate-kernel vector to be zero when
the remaining square coordinate minor is nonsingular. -/
theorem flagSlice_eq_zero_of_two_zeros {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ)
    (hdet : ∀ p q, (flagDoubleMinor X p q).det ≠ 0)
    (x : Fin (r + 2) → ℝ) (hx : X *ᵥ x = 0)
    (p q : Fin (r + 2)) (hpq : p ≠ q) (hp : x p = 0) (hq : x q = 0) :
    x = 0 := by
  obtain hqp | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove p q
  · exact (hpq hqp.symm).elim
  have hrest : X.submatrix id p.succAbove *ᵥ (fun i => x (p.succAbove i)) = 0 :=
    (mulVec_delete_zero X x p hp).trans hx
  have hz : (fun i => x (p.succAbove i)) = 0 :=
    sliceMatrix_kernel_eq_zero_of_coord_zero (X.submatrix id p.succAbove) j
      (hdet p j) _ hrest hq
  funext i
  refine Fin.succAboveCases p ?_ (fun j => ?_) i
  · exact hp
  · exact congrFun hz j

/-- A mass-one coordinate solution cannot have two distinct zero coefficients. -/
theorem flagSlice_no_two_zeros {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ)
    (hdet : ∀ p q, (flagDoubleMinor X p q).det ≠ 0)
    (x : Fin (r + 2) → ℝ) (hmass : ∑ i, x i = 1) (hx : X *ᵥ x = 0)
    (p q : Fin (r + 2)) (hp : x p = 0) (hq : x q = 0) : p = q := by
  by_contra hpq
  have hz := flagSlice_eq_zero_of_two_zeros X hdet x hx p q hpq hp hq
  simp [hz] at hmass

/-- The next height coordinate is nonconstant along every nonzero kernel direction. -/
theorem flagSlice_height_slope_ne_zero {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hdet : (flagPrependRow z (flagConstraintMatrix X)).det ≠ 0)
    (w : Fin (r + 2) → ℝ) (hw : flagConstraintMatrix X *ᵥ w = 0) (hne : w ≠ 0) :
    ∑ i, w i * z i ≠ 0 := by
  intro hz
  have hu : IsUnit (flagPrependRow z (flagConstraintMatrix X)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  apply hne
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hz' : ∑ i, z i * w i = 0 := by simpa only [mul_comm] using hz
  rw [Matrix.mulVec_zero, flagPrependRow_mulVec, hz', hw]
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- A boundary point of the mass-one slice has nonzero next height. -/
theorem flagSlice_boundary_height_ne_zero {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hdet : ∀ p, (sliceDeleteColumn (flagPrependRow z X) p).det ≠ 0)
    (x : Fin (r + 2) → ℝ) (hmass : ∑ i, x i = 1) (hx : X *ᵥ x = 0)
    (p : Fin (r + 2)) (hp : x p = 0) : ∑ i, x i * z i ≠ 0 := by
  intro hz
  have hkernel : (flagPrependRow z X) *ᵥ x = 0 := by
    have hz' : ∑ i, z i * x i = 0 := by simpa only [mul_comm] using hz
    rw [flagPrependRow_mulVec, hz', hx]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have heq := sliceMatrix_kernel_eq_zero_of_coord_zero (flagPrependRow z X) p
    (hdet p) x hkernel hp
  simp [heq] at hmass

/-- Produce the line and all the nondegeneracy hypotheses of the interval lemmas
from the concrete determinant conditions, for the actual mass-one equations. -/
theorem exists_flagSlice_line {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hG : FlagSliceGeneric X z) :
    ∃ a w : Fin (r + 2) → ℝ,
      (∑ i, a i) = 1 ∧ X *ᵥ a = 0 ∧ (∑ i, w i) = 0 ∧ X *ᵥ w = 0 ∧
      w ≠ 0 ∧ (∀ i, w i ≠ 0) ∧ sliceNoDoubleZero a w ∧
      (∑ i, w i * z i) ≠ 0 ∧
      (∀ x, ((∑ i, x i) = 1 ∧ X *ᵥ x = 0) ↔ ∃ t : ℝ, x = sliceCoeff a w t) := by
  obtain ⟨a, w, ha, hw, hne, hwi, hline⟩ :=
    exists_sliceMatrix_line (flagConstraintMatrix X) hG.mass_minors (Fin.cons 1 0)
  have ha' := (flagConstraintMatrix_eq_rhs_iff X a).mp ha
  have hw' := (flagConstraintMatrix_eq_zero_iff X w).mp hw
  have hline' : ∀ x, ((∑ i, x i) = 1 ∧ X *ᵥ x = 0) ↔
      ∃ t : ℝ, x = sliceCoeff a w t := by
    intro x
    rw [← flagConstraintMatrix_eq_rhs_iff]
    exact hline x
  refine ⟨a, w, ha'.1, ha'.2, hw'.1, hw'.2, hne, hwi, ?_,
    flagSlice_height_slope_ne_zero X z hG.augmented_height w hw hne, hline'⟩
  intro i j t hi hj
  have ht := (hline' (sliceCoeff a w t)).mpr ⟨t, rfl⟩
  exact flagSlice_no_two_zeros X hG.coordinate_minors _ ht.1 ht.2 i j hi hj

end VCDimConvexBound
