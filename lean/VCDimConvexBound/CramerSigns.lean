import VCDimConvexBound.ConvexCertificates
import VCDimConvexBound.SignPatterns
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Cramer certificates and the signs of determinant ratios

This file supplies the nonsingular part of minor-sign reconstruction. A square
augmented simplex has convex membership determined by its determinant and the
determinants obtained by replacing one column. `MinorIndependence` and
`MinorHullRecovery` supply row selection and consistency of the remaining
rows for general lower-dimensional supports.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

theorem signCode_eq_iff (a b : ℝ) :
    signCode a = signCode b ↔ (a < 0 ↔ b < 0) ∧ (a = 0 ↔ b = 0) := by
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;>
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;>
      simp_all only [signCode] <;> norm_num at * <;> decide

theorem nonneg_iff_of_signCode_eq {a b : ℝ} (h : signCode a = signCode b) :
    0 ≤ a ↔ 0 ≤ b := by
  have hlt := ((signCode_eq_iff a b).mp h).1
  simpa only [not_lt] using not_congr hlt

theorem nonpos_iff_of_signCode_eq {a b : ℝ} (h : signCode a = signCode b) :
    a ≤ 0 ↔ b ≤ 0 := by
  obtain ⟨hlt, heq⟩ := (signCode_eq_iff a b).mp h
  simpa only [le_iff_lt_or_eq] using or_congr hlt heq

theorem div_nonneg_iff_of_signCode_eq {a b c d : ℝ}
    (hn : signCode a = signCode b) (hd : signCode c = signCode d) :
    0 ≤ a / c ↔ 0 ≤ b / d := by
  simp only [div_nonneg_iff, nonneg_iff_of_signCode_eq hn,
    nonneg_iff_of_signCode_eq hd, nonpos_iff_of_signCode_eq hn,
    nonpos_iff_of_signCode_eq hd]

/-- Normalized Cramer numerators; useful only under a nonzero determinant hypothesis. -/
noncomputable def cramerWeights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (b : ι → ℝ) : ι → ℝ := A.det⁻¹ • A.cramer b

theorem cramerWeights_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (b : ι → ℝ) (i : ι) :
    cramerWeights A b i = (A.updateCol i b).det / A.det := by
  simp [cramerWeights, Matrix.cramer_apply, div_eq_mul_inv, mul_comm]

theorem mulVec_cramerWeights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (b : ι → ℝ) (hA : A.det ≠ 0) :
    A *ᵥ cramerWeights A b = b := by
  rw [cramerWeights, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
    inv_mul_cancel₀ hA, one_smul]

theorem cramerWeights_eq_of_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (b w : ι → ℝ) (hA : A.det ≠ 0) (hw : A *ᵥ w = b) :
    cramerWeights A b = w :=
  Matrix.mulVec_injective_of_det_ne_zero hA ((mulVec_cramerWeights A b hA).trans hw.symm)

/-- Determinant signs preserve the nonnegativity of every Cramer coefficient. -/
theorem cramerWeights_nonneg_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (a b : ι → ℝ)
    (hd : signCode A.det = signCode B.det)
    (hc : ∀ i, signCode (A.updateCol i a).det = signCode (B.updateCol i b).det) :
    (∀ i, 0 ≤ cramerWeights A a i) ↔ (∀ i, 0 ≤ cramerWeights B b i) := by
  simp only [cramerWeights_apply]
  exact forall_congr' fun i => div_nonneg_iff_of_signCode_eq (hc i) hd

/-- Square augmented point matrix, with `D+1` columns. -/
def simplexMatrix {D : ℕ} (q : Option (Fin D) → Point D) :
    Matrix (Option (Fin D)) (Option (Fin D)) ℝ := Matrix.of fun r i => augmentedPoint (q i) r

theorem simplexMatrix_mulVec {D : ℕ} (q : Option (Fin D) → Point D)
    (w : Option (Fin D) → ℝ) :
    simplexMatrix q *ᵥ w = ∑ i, w i • augmentedPoint (q i) := by
  ext r
  simp [simplexMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- For an invertible augmented simplex, convex membership is exactly nonnegative Cramer weights. -/
theorem mem_simplex_iff_cramerWeights_nonneg {D : ℕ}
    (q : Option (Fin D) → Point D) (x : Point D) (hq : (simplexMatrix q).det ≠ 0) :
    x ∈ convexHull ℝ (Set.range q) ↔
      ∀ i, 0 ≤ cramerWeights (simplexMatrix q) (augmentedPoint x) i := by
  rw [mem_convexHull_range_iff_augmented]
  constructor
  · rintro ⟨w, hw, hx⟩
    have he := cramerWeights_eq_of_mulVec (simplexMatrix q) (augmentedPoint x) w hq
      (by simpa [simplexMatrix_mulVec] using hx)
    simpa only [he] using hw
  · intro hw
    refine ⟨cramerWeights (simplexMatrix q) (augmentedPoint x), hw, ?_⟩
    rw [← simplexMatrix_mulVec]
    exact mulVec_cramerWeights _ _ hq

/-- The nonsingular simplex case of convex membership invariance under equal minor signs. -/
theorem mem_simplex_iff_of_same_signs {D : ℕ}
    (q q' : Option (Fin D) → Point D) (x x' : Point D)
    (hq : (simplexMatrix q).det ≠ 0)
    (hd : signCode (simplexMatrix q).det = signCode (simplexMatrix q').det)
    (hc : ∀ i, signCode ((simplexMatrix q).updateCol i (augmentedPoint x)).det =
      signCode ((simplexMatrix q').updateCol i (augmentedPoint x')).det) :
    x ∈ convexHull ℝ (Set.range q) ↔ x' ∈ convexHull ℝ (Set.range q') := by
  have hq' : (simplexMatrix q').det ≠ 0 :=
    fun h => hq (((signCode_eq_iff _ _).mp hd).2.mpr h)
  rw [mem_simplex_iff_cramerWeights_nonneg q x hq,
    mem_simplex_iff_cramerWeights_nonneg q' x' hq']
  exact cramerWeights_nonneg_iff _ _ _ _ hd hc

end VCDimConvexBound
