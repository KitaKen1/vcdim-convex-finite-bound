import VCDimConvexBound.PolynomialPartialDerivative

/-!
# A polynomial barrier with finitely many critical points

Subtracting a positive multiple of `1 + sum x_j^(2d+2)` from `P^2`
forces the critical equations into the pure-power form. The resulting
bound applies even to degenerate critical points.
-/

namespace VCDimConvexBound

open scoped BigOperators

variable {σ τ : Type*} [Fintype σ]

theorem barrierPower_nonneg (d : ℕ) (x : ℝ) : 0 ≤ x ^ (2 * d + 2) := by
  rw [show 2 * d + 2 = (d + 1) * 2 by omega, pow_mul]
  exact sq_nonneg _

/-- The squared polynomial with a separable even-power barrier. -/
noncomputable def polynomialBarrier (P : MvPolynomial σ ℝ) (d : ℕ) (ε : ℝ) :
    MvPolynomial σ ℝ :=
  P ^ 2 - MvPolynomial.C ε * (1 + ∑ j, MvPolynomial.X j ^ (2 * d + 2))

theorem eval_polynomialBarrier (P : MvPolynomial σ ℝ) (d : ℕ) (ε : ℝ) (x : σ → ℝ) :
    MvPolynomial.eval x (polynomialBarrier P d ε) =
      MvPolynomial.eval x P ^ 2 - ε * (1 + ∑ j, x j ^ (2 * d + 2)) := by
  simp [polynomialBarrier]

/-- The low-degree right-hand side of the j-th critical equation. -/
noncomputable def barrierCriticalPolynomial (P : MvPolynomial σ ℝ) (d : ℕ)
    (ε : ℝ) (j : σ) : MvPolynomial σ ℝ :=
  MvPolynomial.C (ε * (2 * d + 2 : ℕ))⁻¹ * MvPolynomial.pderiv j (P ^ 2)

theorem totalDegree_barrierCriticalPolynomial_lt (P : MvPolynomial σ ℝ)
    (d : ℕ) (ε : ℝ) (hP : P.totalDegree ≤ d) (j : σ) :
    (barrierCriticalPolynomial P d ε j).totalDegree < 2 * d + 1 := by
  have h := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (ε * (2 * d + 2 : ℕ))⁻¹) (MvPolynomial.pderiv j (P ^ 2))
  have hp := MvPolynomial.totalDegree_pow P 2
  have hd := totalDegree_pderiv_le (P ^ 2) j
  simp only [MvPolynomial.totalDegree_C, zero_add] at h
  change _ < _
  dsimp [barrierCriticalPolynomial]
  omega

theorem eval_pderiv_polynomialBarrier (P : MvPolynomial σ ℝ) (d : ℕ) (ε : ℝ)
    (x : σ → ℝ) (j : σ) :
    MvPolynomial.eval x (MvPolynomial.pderiv j (polynomialBarrier P d ε)) =
      MvPolynomial.eval x (MvPolynomial.pderiv j (P ^ 2)) -
        ε * (2 * d + 2 : ℕ) * x j ^ (2 * d + 1) := by
  classical
  simp [polynomialBarrier, Pi.single_apply, mul_ite, mul_assoc]

/-- All local maxima obey the same pure-power equations. -/
theorem pure_power_relation_of_barrier_isLocalMax (P : MvPolynomial σ ℝ)
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) (x : σ → ℝ)
    (hx : IsLocalMax (fun y => MvPolynomial.eval y (polynomialBarrier P d ε)) x)
    (j : σ) :
    x j ^ (2 * d + 1) = MvPolynomial.eval x (barrierCriticalPolynomial P d ε j) := by
  have he := eval_pderiv_eq_zero_of_isLocalMax (polynomialBarrier P d ε) x hx j
  rw [eval_pderiv_polynomialBarrier, sub_eq_zero] at he
  have hden : ε * (2 * d + 2 : ℕ) ≠ 0 := by positivity
  simp only [barrierCriticalPolynomial, map_mul, MvPolynomial.eval_C]
  rw [he, ← mul_assoc, inv_mul_cancel₀ hden, one_mul]

/-- Any finite family of distinct local maxima satisfies the required degree bound. -/
theorem card_barrier_localMax_le [Fintype τ] (P : MvPolynomial σ ℝ)
    (d : ℕ) (hP : P.totalDegree ≤ d) (ε : ℝ) (hε : 0 < ε)
    (x : τ → σ → ℝ) (hinj : Function.Injective x)
    (hx : ∀ a, IsLocalMax (fun y => MvPolynomial.eval y (polynomialBarrier P d ε)) (x a)) :
    Fintype.card τ ≤ (2 * d + 1) ^ Fintype.card σ := by
  apply card_le_pow_of_pure_power_relations x hinj (2 * d + 1)
    (barrierCriticalPolynomial P d ε)
  · exact totalDegree_barrierCriticalPolynomial_lt P d ε hP
  · exact fun a j => pure_power_relation_of_barrier_isLocalMax P d ε hε (x a) (hx a) j

end VCDimConvexBound
