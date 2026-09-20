import VCDimConvexBound.PurePowerRootCount
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Formal partial derivatives and local extrema

The direct sign-count route only needs a weak degree estimate for partial
derivatives. A one-coordinate restriction connects formal differentiation
to the ordinary real derivative, avoiding a general Jacobian interface.
-/

namespace VCDimConvexBound

open scoped BigOperators

variable {σ : Type*}

/-- Formal partial differentiation does not increase total degree. -/
theorem totalDegree_pderiv_le [Fintype σ] (P : MvPolynomial σ ℝ) (j : σ) :
    (MvPolynomial.pderiv j P).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro a ha
  have ha' : a + Finsupp.single j 1 ∈ P.support := by
    apply MvPolynomial.mem_support_iff.mpr
    have h := MvPolynomial.mem_support_iff.mp ha
    rw [MvPolynomial.coeff_pderiv] at h
    exact (mul_ne_zero_iff.mp h).1
  have hd := exponent_sum_le_totalDegree ha'
  simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hd
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  omega

/-- Restriction to one varying coordinate has the expected formal partial derivative. -/
theorem hasDerivAt_eval_update [DecidableEq σ] (P : MvPolynomial σ ℝ)
    (x : σ → ℝ) (j : σ) (t : ℝ) :
    HasDerivAt (fun u => MvPolynomial.eval (Function.update x j u) P)
      (MvPolynomial.eval (Function.update x j t) (MvPolynomial.pderiv j P)) t := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa [MvPolynomial.pderiv_C] using hasDerivAt_const t c
  | add P Q hP hQ => simpa only [map_add] using hP.fun_add hQ
  | mul_X P i hP =>
    by_cases hij : i = j
    · subst i
      simpa [MvPolynomial.pderiv_mul, mul_comm, add_comm] using hP.fun_mul (hasDerivAt_id t)
    · simpa [MvPolynomial.pderiv_mul, hij, mul_comm] using hP.mul_const (x i)

/-- Every formal partial derivative vanishes at a local maximum of a real polynomial. -/
theorem eval_pderiv_eq_zero_of_isLocalMax (P : MvPolynomial σ ℝ) (x : σ → ℝ)
    (hx : IsLocalMax (fun y => MvPolynomial.eval y P) x) (j : σ) :
    MvPolynomial.eval x (MvPolynomial.pderiv j P) = 0 := by
  classical
  have hx' : IsLocalMax (fun y => MvPolynomial.eval y P) (Function.update x j (x j)) := by
    simpa using hx
  have hm := hx'.comp_continuous
    (continuous_const.update j continuous_id).continuousAt
  simpa using hm.hasDerivAt_eq_zero (hasDerivAt_eval_update P x j (x j))

end VCDimConvexBound
