import VCDimConvexBound.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Polynomial minors of an augmented additive array

The variables are the `D * m * D` coordinates of the input points. A column
is `(1, gridSum z i)`. We include every row subset and every choice of one
column per selected row. Repeated columns are allowed; their determinants
are zero. This avoids an extra factorial in the bound on the number of minors.

The constant row has degree zero, so every minor has degree at most `D`,
including the minors of size `D + 1`. No general-position hypothesis is used.
Convex-hull membership recovery is proved separately in `MinorHullRecovery`.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The coordinates of the `D` families of `m` points in dimension `D`. -/
abbrev ArrayVar (D m : ℕ) := Fin D × Fin m × Fin D

@[simp] theorem card_arrayVar (D m : ℕ) :
    Fintype.card (ArrayVar D m) = D ^ 2 * m := by
  simp [ArrayVar]
  ring

/-- Assign the point coordinates to the formal variables. -/
def arrayAssignment {D m : ℕ} (z : Fin D → Fin m → Point D) : ArrayVar D m → ℝ :=
  fun v => z v.1 v.2.1 v.2.2

/-- Each coordinate of an additive-array point is a linear polynomial. -/
noncomputable def gridPolynomial {D m : ℕ} (i : Grid D m) (a : Fin D) :
    MvPolynomial (ArrayVar D m) ℝ :=
  ∑ k : Fin D, MvPolynomial.X (k, i k, a)

theorem eval_gridPolynomial {D m : ℕ} (z : Fin D → Fin m → Point D)
    (i : Grid D m) (a : Fin D) :
    MvPolynomial.eval (arrayAssignment z) (gridPolynomial i a) = gridSum z i a := by
  simp [gridPolynomial, arrayAssignment, gridSum, Finset.sum_apply]

theorem totalDegree_gridPolynomial_le {D m : ℕ} (i : Grid D m) (a : Fin D) :
    (gridPolynomial i a).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  simp

/-- `none` is the constant row, and `some a` is coordinate row `a`. -/
noncomputable def augmentedPolynomial {D m : ℕ}
    (r : Option (Fin D)) (i : Grid D m) : MvPolynomial (ArrayVar D m) ℝ :=
  r.elim 1 (gridPolynomial i)

/-- Rowwise degree budget of an augmented column. -/
def rowDegree {D : ℕ} (r : Option (Fin D)) : ℕ := r.elim 0 (fun _ => 1)

theorem totalDegree_augmentedPolynomial_le {D m : ℕ}
    (r : Option (Fin D)) (i : Grid D m) :
    (augmentedPolynomial r i).totalDegree ≤ rowDegree r := by
  cases r with
  | none => simp [augmentedPolynomial, rowDegree]
  | some a => exact totalDegree_gridPolynomial_le i a

/-- A useful rowwise degree bound for determinants of polynomial matrices. -/
theorem totalDegree_det_le {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ ℝ)) (d : ι → ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d i) :
    A.det.totalDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s _
  calc
    _ ≤ (∏ i, A (s i) i).totalDegree := MvPolynomial.totalDegree_smul_le _ _
    _ ≤ ∑ i, (A (s i) i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i, d (s i) := Finset.sum_le_sum fun i _ => hA (s i) i
    _ = ∑ i, d i := Equiv.sum_comp s d

/-- A row subset and an arbitrary column indexed by each selected row. -/
abbrev MinorIndex (D m : ℕ) :=
  Σ R : Finset (Option (Fin D)), (R → Grid D m)

/-- The determinant of the square submatrix specified by a minor index. -/
noncomputable def minorPolynomial {D m : ℕ} (j : MinorIndex D m) :
    MvPolynomial (ArrayVar D m) ℝ := by
  classical
  exact Matrix.det (Matrix.of (fun r s : j.1 => augmentedPolynomial r.val (j.2 s)))

/-- Evaluation gives precisely the corresponding augmented real determinant. -/
theorem eval_minorPolynomial {D m : ℕ} (z : Fin D → Fin m → Point D)
    (j : MinorIndex D m) :
    MvPolynomial.eval (arrayAssignment z) (minorPolynomial j) =
      Matrix.det (Matrix.of (fun r s : j.1 => r.val.elim 1 (gridSum z (j.2 s)))) := by
  classical
  rw [minorPolynomial, RingHom.map_det]
  congr 1
  ext r s
  change MvPolynomial.eval (arrayAssignment z) (augmentedPolynomial r.val (j.2 s)) =
    r.val.elim 1 (gridSum z (j.2 s))
  cases h : r.val with
  | none => simp [augmentedPolynomial]
  | some a => simpa [augmentedPolynomial] using eval_gridPolynomial z (j.2 s) a

/-- At most `D` nonconstant rows can occur in any selected row subset. -/
theorem sum_rowDegree_le (D : ℕ) (R : Finset (Option (Fin D))) :
    (∑ r : R, rowDegree r.val) ≤ D := by
  classical
  calc
    (∑ r : R, rowDegree r.val) = ∑ r ∈ R, rowDegree r := by
      simp only [Finset.sum_coe_sort]
    _ ≤ ∑ r : Option (Fin D), rowDegree r :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = D := by simp [Fintype.sum_option, rowDegree]

/-- All minors, including size `D+1`, have total degree at most `D`. -/
theorem totalDegree_minorPolynomial_le {D m : ℕ} (j : MinorIndex D m) :
    (minorPolynomial j).totalDegree ≤ D := by
  classical
  exact (totalDegree_det_le _ (fun r : j.1 => rowDegree r.val)
    (fun r s => totalDegree_augmentedPolynomial_le r.val (j.2 s))).trans
      (sum_rowDegree_le D j.1)

/-- The family contains at most `2^(D+1) * M^(D+1)` minors, where `M=m^D`. -/
theorem card_minorIndex_le (D m : ℕ) (hm : 0 < m) :
    Fintype.card (MinorIndex D m) ≤ 2 ^ (D + 1) * (m ^ D) ^ (D + 1) := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ R : Finset (Option (Fin D)), Fintype.card (R → Grid D m))
        = ∑ R : Finset (Option (Fin D)), (m ^ D) ^ R.card := by simp
    _ ≤ ∑ _R : Finset (Option (Fin D)), (m ^ D) ^ (D + 1) := by
      apply Finset.sum_le_sum
      intro R _
      apply Nat.pow_le_pow_right (by positivity)
      simpa using Finset.card_le_univ R
    _ = 2 ^ (D + 1) * (m ^ D) ^ (D + 1) := by simp

/-- The constant-row singleton already supplies one index for every grid point. -/
theorem card_grid_le_minorIndex (D m : ℕ) :
    m ^ D ≤ Fintype.card (MinorIndex D m) := by
  classical
  let e : Grid D m → MinorIndex D m := fun i => ⟨{none}, fun _ => i⟩
  have he : Function.Injective e := by
    intro i j h
    have h' : (fun _ : ({none} : Finset (Option (Fin D))) => i) =
        (fun _ : ({none} : Finset (Option (Fin D))) => j) :=
      eq_of_heq (Sigma.mk.inj h).2
    exact congrFun h' ⟨none, by simp⟩
  simpa using Fintype.card_le_of_injective e he

/-- A sufficient side-length condition for Warren after adding the perturbation variable. -/
theorem minor_warren_size_condition (D m : ℕ) (hD : 2 ≤ D) (hm : D ^ 2 ≤ m) :
    D ^ 2 * m + 1 ≤ 2 * Fintype.card (MinorIndex D m) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hpow : m ^ 2 ≤ m ^ D := Nat.pow_le_pow_right hm0 hD
  have hmul : D ^ 2 * m ≤ m ^ 2 := by nlinarith
  have hm2 : 1 ≤ m ^ 2 := Nat.succ_le_of_lt (pow_pos hm0 2)
  have hcard := card_grid_le_minorIndex D m
  omega

end VCDimConvexBound
