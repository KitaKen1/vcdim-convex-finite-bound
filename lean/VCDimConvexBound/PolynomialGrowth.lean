import VCDimConvexBound.PolynomialBarrier
import Mathlib.Topology.Order.Compact

/-!
# Explicit polynomial growth and the barrier on a box boundary

Coefficient absolute values provide an elementary uniform bound on a box.
This is enough to keep a positive maximum away from its boundary.
-/

namespace VCDimConvexBound

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

noncomputable def polynomialCoeffAbsSum (P : MvPolynomial σ ℝ) : ℝ :=
  ∑ a ∈ P.support, |P.coeff a|

omit [Fintype σ] in
theorem polynomialCoeffAbsSum_nonneg (P : MvPolynomial σ ℝ) :
    0 ≤ polynomialCoeffAbsSum P := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_eval_monomial_le (a : σ →₀ ℕ) (c : ℝ) (x : σ → ℝ)
    (R : ℝ) (hx : ∀ j, |x j| ≤ R) :
    |MvPolynomial.eval x (MvPolynomial.monomial a c)| ≤ |c| * R ^ (∑ j, a j) := by
  classical
  rw [MvPolynomial.eval_monomial, abs_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finset.abs_prod]
  simp only [abs_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun j _ => pow_nonneg (abs_nonneg _) _)
    (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hx j) _)

/-- A degree-d polynomial grows at most like R^d on the coordinate box. -/
theorem abs_eval_le_coeffAbsSum_mul_pow (P : MvPolynomial σ ℝ) (d : ℕ)
    (hP : P.totalDegree ≤ d) (x : σ → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (hx : ∀ j, |x j| ≤ R) :
    |MvPolynomial.eval x P| ≤ polynomialCoeffAbsSum P * R ^ d := by
  classical
  calc
    _ ≤ ∑ a ∈ P.support, |MvPolynomial.eval x (MvPolynomial.monomial a (P.coeff a))| := by
      conv_lhs => rw [MvPolynomial.as_sum P, map_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ P.support, |P.coeff a| * R ^ d := by
      apply Finset.sum_le_sum
      intro a ha
      exact (abs_eval_monomial_le a _ x R hx).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hR ((exponent_sum_le_totalDegree ha).trans hP)) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- A sufficiently large box has a strictly negative barrier on its boundary. -/
theorem eval_barrier_neg_on_box_boundary (P : MvPolynomial σ ℝ) (d : ℕ)
    (hP : P.totalDegree ≤ d) (ε : ℝ) (hε : 0 < ε) (R : ℝ) (hR : 1 ≤ R)
    (hlarge : polynomialCoeffAbsSum P ^ 2 < ε * R ^ 2)
    (x : σ → ℝ) (hx : ∀ j, |x j| ≤ R) (j : σ) (hj : |x j| = R) :
    MvPolynomial.eval x (polynomialBarrier P d ε) < 0 := by
  have hg := abs_eval_le_coeffAbsSum_mul_pow P d hP x R hR hx
  have hc := polynomialCoeffAbsSum_nonneg P
  have hr : 0 < R := by linarith
  have hs : R ^ (2 * d + 2) ≤ ∑ i, x i ^ (2 * d + 2) := by
    have he : x j ^ (2 * d + 2) = R ^ (2 * d + 2) := by
      rw [← hj, ← abs_pow, abs_of_nonneg (barrierPower_nonneg d (x j))]
    rw [← he]
    exact Finset.single_le_sum (f := fun i => x i ^ (2 * d + 2))
      (fun i _ => barrierPower_nonneg d (x i)) (Finset.mem_univ j)
  have hg2 : MvPolynomial.eval x P ^ 2 ≤ polynomialCoeffAbsSum P ^ 2 * R ^ (2 * d) := by
    calc
      _ = |MvPolynomial.eval x P| ^ 2 := (sq_abs _).symm
      _ ≤ (polynomialCoeffAbsSum P * R ^ d) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hg 2
      _ = _ := by rw [mul_pow, ← pow_mul]; congr 1; congr 1; omega
  have ht := mul_lt_mul_of_pos_right hlarge (pow_pos hr (2 * d))
  have hp : ε * R ^ 2 * R ^ (2 * d) = ε * R ^ (2 * d + 2) := by
    rw [mul_assoc, ← pow_add]; congr 2; omega
  rw [hp] at ht
  rw [eval_polynomialBarrier]
  nlinarith

end VCDimConvexBound
