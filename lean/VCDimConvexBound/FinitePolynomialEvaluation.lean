import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Polynomial interpolation on finitely many distinct points

Coordinate differences separate points over any field. Products of these
linear polynomials give the delta functions, so evaluation onto a finite
set of distinct points is a surjective linear map.
-/

namespace VCDimConvexBound

open scoped BigOperators

variable {K σ τ : Type*} [Field K]

/-- Evaluate a polynomial simultaneously at an indexed family of points. -/
noncomputable def polynomialEvaluation (x : τ → σ → K) :
    MvPolynomial σ K →ₗ[K] (τ → K) where
  toFun P a := MvPolynomial.eval (x a) P
  map_add' P Q := by ext a; simp
  map_smul' c P := by ext a; simp

@[simp]
theorem polynomialEvaluation_apply (x : τ → σ → K) (P : MvPolynomial σ K) (a : τ) :
    polynomialEvaluation x P a = MvPolynomial.eval (x a) P := rfl

/-- One coordinate difference separates any two different points. -/
theorem exists_polynomial_separating_points {a b : σ → K} (hab : a ≠ b) :
    ∃ P : MvPolynomial σ K, MvPolynomial.eval a P = 1 ∧ MvPolynomial.eval b P = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ b j := by
    by_contra! h
    exact hab (funext h)
  refine ⟨MvPolynomial.C (a j - b j)⁻¹ *
    (MvPolynomial.X j - MvPolynomial.C (b j)), ?_, ?_⟩
  · simp [sub_ne_zero.mpr hj]
  · simp

/-- A multivariate polynomial realizes the delta function at any chosen point. -/
theorem exists_polynomial_eval_delta [Fintype τ] [DecidableEq τ]
    (x : τ → σ → K) (hx : Function.Injective x) (a : τ) :
    ∃ P : MvPolynomial σ K, ∀ b, MvPolynomial.eval (x b) P = if b = a then 1 else 0 := by
  classical
  have hsep (b : {b : τ // b ≠ a}) : ∃ P : MvPolynomial σ K,
      MvPolynomial.eval (x a) P = 1 ∧ MvPolynomial.eval (x b.val) P = 0 :=
    exists_polynomial_separating_points (fun h => b.property (hx h.symm))
  choose P hP using hsep
  refine ⟨∏ b, P b, fun b => ?_⟩
  by_cases hba : b = a
  · subst b
    simp [hP]
  · rw [if_neg hba, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨b, hba⟩) (hP ⟨b, hba⟩).2

/-- Every function on a finite family of distinct points is a polynomial evaluation. -/
theorem polynomialEvaluation_surjective [Fintype τ]
    (x : τ → σ → K) (hx : Function.Injective x) :
    Function.Surjective (polynomialEvaluation x) := by
  classical
  choose P hP using exists_polynomial_eval_delta x hx
  intro y
  refine ⟨∑ a, MvPolynomial.C (y a) * P a, ?_⟩
  ext b
  simp [hP, mul_ite]

/-- Coefficients only scale a monomial's simultaneous evaluation vector. -/
theorem polynomialEvaluation_monomial_smul (x : τ → σ → K) (a : σ →₀ ℕ) (c : K) :
    polynomialEvaluation x (MvPolynomial.monomial a c) =
      c • polynomialEvaluation x (MvPolynomial.monomial a 1) := by
  ext b
  simp [MvPolynomial.eval_monomial]

end VCDimConvexBound
