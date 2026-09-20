import VCDimConvexBound.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Avoiding finitely many polynomial zero sets in an arbitrary neighbourhood

A real multivariate polynomial vanishing on an open box is the zero
polynomial. Taking a product yields simultaneous avoidance for any finite
family of nonzero polynomials. No degree estimate or special path is needed.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- A nonzero real polynomial cannot vanish throughout a nonempty open set. -/
theorem exists_mvPolynomial_ne_zero_mem_open {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (hP : P ≠ 0) (U : Set (σ → ℝ)) (hU : IsOpen U)
    (a : σ → ℝ) (ha : a ∈ U) :
    ∃ b ∈ U, MvPolynomial.eval b P ≠ 0 := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU a ha
  by_contra! hzero
  apply hP
  apply MvPolynomial.funext_set (fun i => Set.Ioo (a i - ε) (a i + ε))
    (fun i => Set.Ioo_infinite (by linarith))
  intro b hb
  rw [map_zero]
  apply hzero b
  apply hball
  apply (dist_pi_lt_iff hε).mpr
  intro i
  have hi := hb i (Set.mem_univ i)
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- Every neighbourhood simultaneously avoids all zeros of finitely many nonzero polynomials. -/
theorem exists_mvPolynomial_family_ne_zero_mem_open {σ ι : Type*}
    [Fintype σ] [Fintype ι] (P : ι → MvPolynomial σ ℝ) (hP : ∀ i, P i ≠ 0)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (a : σ → ℝ) (ha : a ∈ U) :
    ∃ b ∈ U, ∀ i, MvPolynomial.eval b (P i) ≠ 0 := by
  classical
  have hprod : (∏ i, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hP i)
  obtain ⟨b, hb, hval⟩ := exists_mvPolynomial_ne_zero_mem_open (∏ i, P i) hprod U hU a ha
  refine ⟨b, hb, ?_⟩
  have he : (∏ i, MvPolynomial.eval b (P i)) ≠ 0 := by simpa only [map_prod] using hval
  exact fun i => Finset.prod_ne_zero_iff.mp he i (Finset.mem_univ i)

end VCDimConvexBound
