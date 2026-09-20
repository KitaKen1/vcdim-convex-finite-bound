import Mathlib

#eval Lean.versionString

-- The monolithic file elaborates several finite case splits that are spread
-- across modules in the FC build, so it needs a larger per-command budget.
set_option maxHeartbeats 800000

/-!
# A standalone Lean4Web proof of the convex additive VC_n bound

This file is generated from the files in `../lean/VCDimConvexBound/`.
It uses mathlib only.  The definition below is the additive VC_n definition
used by the pinned Formal Conjectures target.  The repository license and
README record the source revision and attribution.
-/

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

/-- A set has additive VC_n dimension at most `d` when no additive family
indexed by `Fin n -> Fin (d + 1)` realizes every subset. -/
def HasAddVCNDimAtMost (A : Set G) (n d : ℕ) : Prop :=
  ∀ (x : Fin n → Fin (d + 1) → G) (y : Set (Fin n → Fin (d + 1)) → G),
    ¬ ∀ i s, y s + ∑ k, x k (i k) ∈ A ↔ i ∈ s


/-! ## Source module `VCDimConvexBound.FinitePolynomialEvaluation` -/


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
  · rw [ite_eq_right hba, map_prod]
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


/-! ## Source module `VCDimConvexBound.PurePowerRootCount` -/


/-!
# Counting roots of pure-power equations

For equations `x_j^q = R_j(x)` with `totalDegree R_j < q`, evaluation
vectors are spanned by monomials whose individual exponents are less than
`q`. Interpolation on distinct points then bounds their number by `q^p`.
No component bound, Bezout theorem, or nondegeneracy hypothesis is used.
-/

namespace VCDimConvexBound

open scoped BigOperators

variable {K σ τ : Type*} [Field K] [Fintype σ]

/-- The exponent vector of a monomial with all exponents less than q. -/
noncomputable def boundedMonomialExponent {q : ℕ} (a : σ → Fin q) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (a j).val)

@[simp]
theorem boundedMonomialExponent_apply {q : ℕ} (a : σ → Fin q) (j : σ) :
    boundedMonomialExponent a j = (a j).val := by
  simp [boundedMonomialExponent]

/-- The span of the q^p small monomial evaluation vectors. -/
noncomputable def boundedMonomialSpan (x : τ → σ → K) (q : ℕ) : Submodule K (τ → K) :=
  Submodule.span K (Set.range fun a : σ → Fin q =>
    polynomialEvaluation x (MvPolynomial.monomial (boundedMonomialExponent a) 1))

/-- A monomial already inside the exponent box belongs to its evaluation span. -/
theorem polynomialEvaluation_monomial_mem_of_bounded (x : τ → σ → K) (q : ℕ)
    (a : σ →₀ ℕ) (ha : ∀ j, a j < q) :
    polynomialEvaluation x (MvPolynomial.monomial a 1) ∈ boundedMonomialSpan x q := by
  classical
  apply Submodule.subset_span
  have he : boundedMonomialExponent (fun j => (⟨a j, ha j⟩ : Fin q)) = a := by
    ext j
    simp
  exact ⟨fun j => ⟨a j, ha j⟩, by simp only [he]⟩

/-- A support exponent's total sum is bounded by the polynomial's total degree. -/
theorem exponent_sum_le_totalDegree {P : MvPolynomial σ K} {a : σ →₀ ℕ}
    (ha : a ∈ P.support) : (∑ j, a j) ≤ P.totalDegree := by
  have h := MvPolynomial.le_totalDegree ha
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h
  exact h

omit [Fintype σ] in
/-- Expand a monomial multiple into its shifted monomials before evaluating. -/
theorem polynomialEvaluation_monomial_mul (x : τ → σ → K) (a : σ →₀ ℕ)
    (P : MvPolynomial σ K) :
    polynomialEvaluation x (MvPolynomial.monomial a 1 * P) =
      ∑ b ∈ P.support,
        polynomialEvaluation x (MvPolynomial.monomial (a + b) (P.coeff b)) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [Finset.mul_sum, MvPolynomial.monomial_mul_monomial, one_mul, map_sum]

/-- Pure-power equations reduce every monomial by induction on total degree. -/
theorem polynomialEvaluation_monomial_mem_of_pure_power_relations
    (x : τ → σ → K) (q : ℕ) (R : σ → MvPolynomial σ K)
    (hR : ∀ j, (R j).totalDegree < q)
    (hx : ∀ a j, x a j ^ q = MvPolynomial.eval (x a) (R j))
    (a : σ →₀ ℕ) :
    polynomialEvaluation x (MvPolynomial.monomial a 1) ∈ boundedMonomialSpan x q := by
  classical
  have hmain : ∀ n : ℕ, ∀ a : σ →₀ ℕ, (∑ j, a j) = n →
      polynomialEvaluation x (MvPolynomial.monomial a 1) ∈ boundedMonomialSpan x q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a han
      by_cases ha : ∀ j, a j < q
      · exact polynomialEvaluation_monomial_mem_of_bounded x q a ha
      push Not at ha
      obtain ⟨j, hj⟩ := ha
      let b := a - Finsupp.single j q
      have hdecomp : b + Finsupp.single j q = a :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)
      have hsum : (∑ i, b i) + q = n := by
        rw [← han, ← hdecomp]
        simp [Finset.sum_add_distrib]
      have heval : polynomialEvaluation x (MvPolynomial.monomial a 1) =
          polynomialEvaluation x (MvPolynomial.monomial b 1 * R j) := by
        ext t
        simp only [polynomialEvaluation_apply, map_mul]
        rw [← hx t j, ← MvPolynomial.eval_X (f := x t) j, ← map_pow, ← map_mul]
        congr 1
        rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul, hdecomp]
      rw [heval, polynomialEvaluation_monomial_mul]
      apply Submodule.sum_mem
      intro c hc
      rw [polynomialEvaluation_monomial_smul]
      apply Submodule.smul_mem
      apply ih (∑ i, (b + c) i) ?_ (b + c) rfl
      have hcdeg := (exponent_sum_le_totalDegree hc).trans_lt (hR j)
      simp only [Finsupp.add_apply, Finset.sum_add_distrib]
      omega
  exact hmain _ a rfl

/-- Every polynomial evaluates in the same q^p-dimensional spanning space. -/
theorem polynomialEvaluation_mem_of_pure_power_relations
    (x : τ → σ → K) (q : ℕ) (R : σ → MvPolynomial σ K)
    (hR : ∀ j, (R j).totalDegree < q)
    (hx : ∀ a j, x a j ^ q = MvPolynomial.eval (x a) (R j))
    (P : MvPolynomial σ K) :
    polynomialEvaluation x P ∈ boundedMonomialSpan x q := by
  classical
  rw [MvPolynomial.as_sum P, map_sum]
  apply Submodule.sum_mem
  intro a _
  rw [polynomialEvaluation_monomial_smul]
  exact Submodule.smul_mem _ _
    (polynomialEvaluation_monomial_mem_of_pure_power_relations x q R hR hx a)

/-- Interpolation fills the whole function space when the points are distinct. -/
theorem boundedMonomialSpan_eq_top_of_pure_power_relations [Fintype τ]
    (x : τ → σ → K) (hinj : Function.Injective x)
    (q : ℕ) (R : σ → MvPolynomial σ K)
    (hR : ∀ j, (R j).totalDegree < q)
    (hx : ∀ a j, x a j ^ q = MvPolynomial.eval (x a) (R j)) :
    boundedMonomialSpan x q = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨P, rfl⟩ := polynomialEvaluation_surjective x hinj y
  exact polynomialEvaluation_mem_of_pure_power_relations x q R hR hx P

/-- Distinct simultaneous roots of the pure-power equations number at most q^p. -/
theorem card_le_pow_of_pure_power_relations [Fintype τ]
    (x : τ → σ → K) (hinj : Function.Injective x)
    (q : ℕ) (R : σ → MvPolynomial σ K)
    (hR : ∀ j, (R j).totalDegree < q)
    (hx : ∀ a j, x a j ^ q = MvPolynomial.eval (x a) (R j)) :
    Fintype.card τ ≤ q ^ Fintype.card σ := by
  classical
  have hspan := boundedMonomialSpan_eq_top_of_pure_power_relations x hinj q R hR hx
  have hd := finrank_le_of_span_eq_top hspan
  simpa [Module.finrank_pi, Module.finrank_self, Fintype.card_fun] using hd

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.PolynomialPartialDerivative` -/


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


/-! ## Source module `VCDimConvexBound.PolynomialBarrier` -/


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


/-! ## Source module `VCDimConvexBound.PolynomialGrowth` -/


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
  exact Finset.prod_le_prod₀ (fun j _ => pow_nonneg (abs_nonneg _) _)
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


/-! ## Source module `VCDimConvexBound.BarrierMaximum` -/


/-!
# Positive maxima of the barrier on closed regions

A large compact coordinate box contains the witness in its interior and
has negative barrier on its boundary. A positive maximum therefore lies
inside both the box and any closed region whose boundary is contained in
the polynomial zero set.
-/

namespace VCDimConvexBound

open scoped BigOperators Topology

variable {σ : Type*} [Fintype σ]

/-- A positive barrier value cannot occur at a zero of P. -/
theorem eval_ne_zero_of_barrier_pos (P : MvPolynomial σ ℝ) (d : ℕ)
    (ε : ℝ) (hε : 0 < ε) (x : σ → ℝ)
    (hx : 0 < MvPolynomial.eval x (polynomialBarrier P d ε)) :
    MvPolynomial.eval x P ≠ 0 := by
  intro hz
  have hs : 0 ≤ ∑ j, x j ^ (2 * d + 2) :=
    Finset.sum_nonneg fun j _ => barrierPower_nonneg d (x j)
  rw [eval_polynomialBarrier, hz] at hx
  nlinarith

/-- A positive witness in a closed region yields an unconstrained positive local maximum. -/
theorem exists_barrier_localMax_mem (P : MvPolynomial σ ℝ) (d : ℕ)
    (hP : P.totalDegree ≤ d) (ε : ℝ) (hε : 0 < ε)
    (K : Set (σ → ℝ)) (hK : IsClosed K)
    (hKlocal : ∀ x ∈ K, MvPolynomial.eval x P ≠ 0 → K ∈ 𝓝 x)
    (a : σ → ℝ) (ha : a ∈ K)
    (hapos : 0 < MvPolynomial.eval a (polynomialBarrier P d ε)) :
    ∃ b ∈ K, 0 < MvPolynomial.eval b (polynomialBarrier P d ε) ∧
      IsLocalMax (fun x => MvPolynomial.eval x (polynomialBarrier P d ε)) b := by
  classical
  let C := polynomialCoeffAbsSum P
  let S := ∑ j, |a j|
  let R := 1 + C ^ 2 / ε + S
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdiv : 0 ≤ C ^ 2 / ε := div_nonneg (sq_nonneg C) hε.le
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have hRpos : 0 < R := by linarith
  have hlarge : polynomialCoeffAbsSum P ^ 2 < ε * R ^ 2 := by
    have hcancel : ε * (C ^ 2 / ε) = C ^ 2 := by
      simpa only [mul_comm] using div_mul_cancel₀ (C ^ 2) (ne_of_gt hε)
    have hbase : C ^ 2 < ε * R := by
      dsimp [R]
      nlinarith [mul_nonneg hε.le hS]
    have hsq : R ≤ R ^ 2 := by nlinarith
    exact hbase.trans_le (mul_le_mul_of_nonneg_left hsq hε.le)
  have hain : ∀ j, |a j| < R := by
    intro j
    have hj : |a j| ≤ S := Finset.single_le_sum (f := fun i => |a i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    dsimp [R]
    linarith
  let box : Set (σ → ℝ) := Set.Icc (fun _ => -R) (fun _ => R)
  have habox : a ∈ box :=
    ⟨fun j => (abs_lt.mp (hain j)).1.le, fun j => (abs_lt.mp (hain j)).2.le⟩
  have hcompact : IsCompact (box ∩ K) := isCompact_Icc.inter_right hK
  obtain ⟨b, hb, hm⟩ := hcompact.exists_isMaxOn ⟨a, habox, ha⟩
    (MvPolynomial.continuous_eval (polynomialBarrier P d ε)).continuousOn
  have hbpos : 0 < MvPolynomial.eval b (polynomialBarrier P d ε) :=
    hapos.trans_le (hm ⟨habox, ha⟩)
  have hble : ∀ j, |b j| ≤ R := fun j => abs_le.mpr ⟨hb.1.1 j, hb.1.2 j⟩
  have hblt : ∀ j, |b j| < R := by
    intro j
    apply lt_of_le_of_ne (hble j)
    intro heq
    have hn := eval_barrier_neg_on_box_boundary P d hP ε hε R hR hlarge b hble j heq
    linarith
  have hboxnhds : box ∈ 𝓝 b := by
    have hopen : IsOpen {x : σ → ℝ | ∀ j, |x j| < R} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_lt (continuous_apply j).abs continuous_const
    apply Filter.mem_of_superset (hopen.mem_nhds hblt)
    intro x hx
    exact ⟨fun j => (abs_lt.mp (hx j)).1.le, fun j => (abs_lt.mp (hx j)).2.le⟩
  refine ⟨b, hb.2, hbpos, hm.isLocalMax ?_⟩
  exact Filter.inter_mem hboxnhds
    (hKlocal b hb.2 (eval_ne_zero_of_barrier_pos P d ε hε b hbpos))

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SignPatterns` -/


/-!
# Strict and ternary sign patterns

The zero-sign perturbation is separated from the still unproved Warren bound.
Definitions quantify over all real inputs; no general-position assumption is imposed.
-/

namespace VCDimConvexBound

/-- A three-valued code: negative = 0, zero = 1, positive = 2. -/
noncomputable def signCode (x : ℝ) : Fin 3 :=
  if x < 0 then 0 else if x = 0 then 1 else 2

/-- Realized ternary sign vectors of a finite family of real functions. -/
noncomputable def ternaryPatterns {ι α : Type*} [Fintype ι]
    (f : ι → α → ℝ) : Finset (ι → Fin 3) := by
  classical
  exact Finset.univ.filter fun s => ∃ x, ∀ i, signCode (f i x) = s i

/-- Realized strict sign vectors: every function must be nonzero at the witness. -/
noncomputable def strictPatterns {ι α : Type*} [Fintype ι]
    (f : ι → α → ℝ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter fun s =>
    ∃ x, ∀ i, if s i then 0 < f i x else f i x < 0

/-- The strict sign-count estimate still to be proved (Warren).
The positive variable and degree hypotheses avoid the zero-dimensional conventions. -/
def WarrenStrictBound : Prop :=
  ∀ (p N k : ℕ), 0 < p → 0 < k → p ≤ N →
    ∀ f : Fin N → MvPolynomial (Fin p) ℝ,
      (∀ i, (f i).totalDegree ≤ k) →
      ((strictPatterns (fun i x => MvPolynomial.eval x (f i))).card : ℝ) ≤
        (4 * Real.exp 1 * k * N / p) ^ p

/-- A finite list has a common positive threshold below all its nonzero absolute values. -/
theorem exists_positive_margin {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, a i ≠ 0 → t < |a i| := by
  classical
  have aux : ∀ s : Finset ι, ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, a i ≠ 0 → t < |a i| := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨t, ht, hs⟩ := ih
      by_cases hi : a i = 0
      · exact ⟨t, ht, by simpa [hi] using hs⟩
      · refine ⟨min t (|a i| / 2), lt_min ht (half_pos (abs_pos.mpr hi)), ?_⟩
        intro j hj hj0
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (abs_pos.mpr hi))
        · exact lt_of_le_of_lt (min_le_left _ _) (hs j hj hj0)
  obtain ⟨t, ht, h⟩ := aux Finset.univ
  exact ⟨t, ht, fun i => h i (Finset.mem_univ i)⟩

/-- Encode a ternary value into the signs of `(f-t, f+t)`. -/
def encodeSign (s : Fin 3) : Bool × Bool :=
  (decide (s = 2), decide (s ≠ 0))

theorem encodeSign_injective : Function.Injective encodeSign := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [encodeSign]

/-- The strict signs of both perturbations recover negative, zero, and positive cases. -/
theorem perturbation_signs (a t : ℝ) (ht : 0 < t)
    (hsmall : a ≠ 0 → t < |a|) :
    (if (encodeSign (signCode a)).1 then 0 < a - t else a - t < 0) ∧
    (if (encodeSign (signCode a)).2 then 0 < a + t else a + t < 0) := by
  by_cases hn : a < 0
  · have ha : a ≠ 0 := ne_of_lt hn
    have h := hsmall ha
    rw [abs_of_neg hn] at h
    rw [signCode, ite_eq_left hn]
    change a - t < 0 ∧ a + t < 0
    constructor <;> linarith
  · by_cases hz : a = 0
    · subst a
      simp [signCode, encodeSign, ht]
    · have hp : 0 < a := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have h := hsmall hz
      rw [abs_of_pos hp] at h
      rw [signCode, ite_eq_right hn, ite_eq_right hz]
      change 0 < a - t ∧ 0 < a + t
      constructor <;> linarith

/-- The two real functions obtained by subtracting and adding one extra real input. -/
def perturbFunctions {ι α : Type*} (f : ι → α → ℝ) :
    (ι × Bool) → (α × ℝ) → ℝ :=
  fun j x => if j.2 then f j.1 x.1 + x.2 else f j.1 x.1 - x.2

/-- The pointwise encoding into two strict signs. -/
def encodePattern {ι : Type*} (s : ι → Fin 3) : ι × Bool → Bool :=
  fun j => if j.2 then (encodeSign (s j.1)).2 else (encodeSign (s j.1)).1

theorem encodePattern_injective {ι : Type*} :
    Function.Injective (encodePattern (ι := ι)) := by
  intro s u h
  funext i
  apply encodeSign_injective
  apply Prod.ext
  · exact congrFun h (i, false)
  · exact congrFun h (i, true)

/-- Every ternary pattern becomes a strict pattern at a suitably small positive perturbation. -/
theorem encodePattern_mem_strictPatterns {ι α : Type*} [Fintype ι]
    (f : ι → α → ℝ) {s : ι → Fin 3} (hs : s ∈ ternaryPatterns f) :
    encodePattern s ∈ strictPatterns (perturbFunctions f) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, ∀ i, signCode (f i x) = s i := by
    simpa [ternaryPatterns] using hs
  obtain ⟨t, ht, hsmall⟩ := exists_positive_margin (fun i => f i x)
  simp only [strictPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(x, t), ?_⟩
  rintro ⟨i, b⟩
  have h := perturbation_signs (f i x) t ht (hsmall i)
  cases b with
  | false => simpa [encodePattern, perturbFunctions, hx i] using h.1
  | true => simpa [encodePattern, perturbFunctions, hx i] using h.2

/-- Zero signs require only one extra real input and twice as many functions.
This counting reduction does not assume Warren's theorem. -/
theorem card_ternaryPatterns_le_strictPatterns_perturb {ι α : Type*} [Fintype ι]
    (f : ι → α → ℝ) :
    (ternaryPatterns f).card ≤ (strictPatterns (perturbFunctions f)).card := by
  classical
  calc
    (ternaryPatterns f).card = ((ternaryPatterns f).image encodePattern).card :=
      (Finset.card_image_of_injective _ encodePattern_injective).symm
    _ ≤ (strictPatterns (perturbFunctions f)).card := by
      apply Finset.card_le_card
      intro s hs
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
      exact encodePattern_mem_strictPatterns f hu

/-- Polynomial realization of the perturbation, with `none` as the new variable. -/
noncomputable def perturbPolynomials {ι σ : Type*}
    (f : ι → MvPolynomial σ ℝ) : ι × Bool → MvPolynomial (Option σ) ℝ :=
  fun j => if j.2 then MvPolynomial.rename some (f j.1) + MvPolynomial.X none
    else MvPolynomial.rename some (f j.1) - MvPolynomial.X none

theorem eval_perturbPolynomials {ι σ : Type*} (f : ι → MvPolynomial σ ℝ)
    (x : σ → ℝ) (t : ℝ) (j : ι × Bool) :
    MvPolynomial.eval (fun o => o.elim t x) (perturbPolynomials f j) =
      perturbFunctions (fun i y => MvPolynomial.eval y (f i)) j (x, t) := by
  rcases j with ⟨i, b⟩
  cases b <;> simp [perturbPolynomials, perturbFunctions, MvPolynomial.eval_rename,
    Function.comp_def]

/-- Adding the one perturbation variable preserves any positive degree bound. -/
theorem totalDegree_perturbPolynomials_le {ι σ : Type*}
    (f : ι → MvPolynomial σ ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hf : ∀ i, (f i).totalDegree ≤ k) (j : ι × Bool) :
    (perturbPolynomials f j).totalDegree ≤ k := by
  rcases j with ⟨i, b⟩
  have hr := (MvPolynomial.totalDegree_rename_le some (f i)).trans (hf i)
  have hX : (MvPolynomial.X (none : Option σ) : MvPolynomial (Option σ) ℝ).totalDegree ≤ k := by
    simpa using hk
  cases b with
  | false => exact (MvPolynomial.totalDegree_sub _ _).trans (max_le hr hX)
  | true => exact (MvPolynomial.totalDegree_add _ _).trans (max_le hr hX)

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.PolynomialSignRegion` -/


/-!
# Closed weak-sign regions and positive barrier maxima

Away from the zero set of the product, weak sign conditions are strict
and give a neighbourhood. The compact-box maximum theorem thus supplies
a local maximum with the required strict signs.
-/

namespace VCDimConvexBound

open scoped BigOperators Topology

variable {σ ι : Type*} [Fintype σ] [Fintype ι]

noncomputable def polynomialWeakSignRegion (f : ι → MvPolynomial σ ℝ) (s : ι → Bool) :
    Set (σ → ℝ) := {x | ∀ i, if s i then 0 ≤ MvPolynomial.eval x (f i)
      else MvPolynomial.eval x (f i) ≤ 0}

omit [Fintype σ] [Fintype ι] in
theorem isClosed_polynomialWeakSignRegion (f : ι → MvPolynomial σ ℝ) (s : ι → Bool) :
    IsClosed (polynomialWeakSignRegion f s) := by
  simp only [polynomialWeakSignRegion, Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  cases hs : s i
  · simpa only [hs, Bool.false_eq_true, ite_false] using
      isClosed_le (MvPolynomial.continuous_eval (f i)) continuous_const
  · simpa only [hs, ite_true] using
      isClosed_le continuous_const (MvPolynomial.continuous_eval (f i))

omit [Fintype σ] in
/-- A nonzero product upgrades all weak signs to strict signs. -/
theorem strict_signs_of_mem_weakSignRegion (f : ι → MvPolynomial σ ℝ) (s : ι → Bool)
    (x : σ → ℝ) (hx : x ∈ polynomialWeakSignRegion f s)
    (hne : MvPolynomial.eval x (∏ i, f i) ≠ 0) :
    ∀ i, if s i then 0 < MvPolynomial.eval x (f i) else MvPolynomial.eval x (f i) < 0 := by
  classical
  rw [map_prod] at hne
  intro i
  have hi := (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  have hwi := hx i
  cases hs : s i <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hwi ⊢
  · exact lt_of_le_of_ne hwi hi
  · exact lt_of_le_of_ne hwi (Ne.symm hi)

omit [Fintype σ] in
/-- Nonzero points of a weak-sign region are interior points. -/
theorem polynomialWeakSignRegion_mem_nhds (f : ι → MvPolynomial σ ℝ) (s : ι → Bool)
    (x : σ → ℝ) (hx : x ∈ polynomialWeakSignRegion f s)
    (hne : MvPolynomial.eval x (∏ i, f i) ≠ 0) :
    polynomialWeakSignRegion f s ∈ 𝓝 x := by
  have hs := strict_signs_of_mem_weakSignRegion f s x hx hne
  have hopen : IsOpen {y : σ → ℝ | ∀ i,
      if s i then 0 < MvPolynomial.eval y (f i) else MvPolynomial.eval y (f i) < 0} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    cases hi : s i
    · simpa only [hi, Bool.false_eq_true, ite_false] using
        isOpen_lt (MvPolynomial.continuous_eval (f i)) continuous_const
    · simpa only [hi, ite_true] using
        isOpen_lt continuous_const (MvPolynomial.continuous_eval (f i))
  apply Filter.mem_of_superset (hopen.mem_nhds hs)
  intro y hy i
  have hi := hy i
  cases hsi : s i <;> simp only [hsi, Bool.false_eq_true, ite_false, ite_true] at hi ⊢
  · exact hi.le
  · exact hi.le

/-- Any positive barrier witness yields a local maximum with exactly the same signs. -/
theorem exists_barrier_localMax_with_signs (f : ι → MvPolynomial σ ℝ)
    (s : ι → Bool) (d : ℕ) (hdeg : (∏ i, f i).totalDegree ≤ d)
    (ε : ℝ) (hε : 0 < ε) (a : σ → ℝ)
    (ha : ∀ i, if s i then 0 < MvPolynomial.eval a (f i) else MvPolynomial.eval a (f i) < 0)
    (hapos : 0 < MvPolynomial.eval a (polynomialBarrier (∏ i, f i) d ε)) :
    ∃ b : σ → ℝ,
      (∀ i, if s i then 0 < MvPolynomial.eval b (f i) else MvPolynomial.eval b (f i) < 0) ∧
      IsLocalMax (fun x => MvPolynomial.eval x (polynomialBarrier (∏ i, f i) d ε)) b := by
  have haw : a ∈ polynomialWeakSignRegion f s := by
    intro i
    have hi := ha i
    cases hs : s i <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hi ⊢
    · exact hi.le
    · exact hi.le
  obtain ⟨b, hb, hbpos, hm⟩ := exists_barrier_localMax_mem (∏ i, f i) d hdeg ε hε
    (polynomialWeakSignRegion f s) (isClosed_polynomialWeakSignRegion f s)
    (polynomialWeakSignRegion_mem_nhds f s) a haw hapos
  exact ⟨b, strict_signs_of_mem_weakSignRegion f s b hb
    (eval_ne_zero_of_barrier_pos (∏ i, f i) d ε hε b hbpos), hm⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.WarrenApplication` -/


/-!
# Applying a strict Warren bound to arbitrary finite polynomial families

Warren's estimate remains an explicit hypothesis. The results here supply the
finite reindexing and the passage from ternary signs to strict signs, including
the extra variable and doubled family. They do not prove Warren's theorem.
-/

namespace VCDimConvexBound

theorem strictPatterns_comp_domain {ι α β : Type*} [Fintype ι]
    (f : ι → α → ℝ) (u : β → α) (hu : Function.Surjective u) :
    strictPatterns (fun i x => f i (u x)) = strictPatterns f := by
  classical
  ext s
  simp only [strictPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨u x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hu x
    exact ⟨y, hx⟩

theorem card_strictPatterns_reindex {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (f : ι → α → ℝ) :
    (strictPatterns (fun i => f (e i))).card = (strictPatterns f).card := by
  classical
  apply Finset.card_bij (fun s _ i => s (e.symm i))
  · intro s hs
    obtain ⟨x, hx⟩ : ∃ x, ∀ i, if s i then 0 < f (e i) x else f (e i) x < 0 := by
      simpa [strictPatterns] using hs
    simp only [strictPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, fun i => by simpa using hx (e.symm i)⟩
  · intro s _ t _ h
    funext i
    simpa using congrFun h (e i)
  · intro s hs
    obtain ⟨x, hx⟩ : ∃ x, ∀ i, if s i then 0 < f i x else f i x < 0 := by
      simpa [strictPatterns] using hs
    refine ⟨fun i => s (e i), ?_, ?_⟩
    · simp only [strictPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, fun i => hx (e i)⟩
    · funext i
      simp

/-- Reindex the finite variable and polynomial types to the `Fin` form of Warren. -/
theorem card_strictPatterns_le_of_warren {ι σ : Type*} [Fintype ι] [Fintype σ]
    (hW : WarrenStrictBound) (k : ℕ) (hp : 0 < Fintype.card σ) (hk : 0 < k)
    (hN : Fintype.card σ ≤ Fintype.card ι) (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ k) :
    ((strictPatterns (fun i x => MvPolynomial.eval x (f i))).card : ℝ) ≤
      (4 * Real.exp 1 * k * Fintype.card ι / Fintype.card σ) ^ Fintype.card σ := by
  classical
  let eι := (Fintype.equivFin ι).symm
  let eσ := Fintype.equivFin σ
  let g := fun i : Fin (Fintype.card ι) => MvPolynomial.rename eσ (f (eι i))
  have hu : Function.Surjective (fun x : Fin (Fintype.card σ) → ℝ => x ∘ eσ) := by
    intro x
    refine ⟨x ∘ eσ.symm, ?_⟩
    funext i
    simp
  have hc : (strictPatterns (fun i x => MvPolynomial.eval x (g i))).card =
      (strictPatterns (fun i x => MvPolynomial.eval x (f i))).card := by
    calc
      _ = (strictPatterns (fun i x => MvPolynomial.eval x (f (eι i)))).card := by
        simpa only [g, MvPolynomial.eval_rename] using congrArg Finset.card
          (strictPatterns_comp_domain (fun i x => MvPolynomial.eval x (f (eι i)))
            (fun x : Fin (Fintype.card σ) → ℝ => x ∘ eσ) hu)
      _ = _ := card_strictPatterns_reindex eι (fun i x => MvPolynomial.eval x (f i))
  rw [← hc]
  exact hW _ _ k hp hk hN g
    (fun i => (MvPolynomial.totalDegree_rename_le eσ _).trans (hf (eι i)))

/-- The strict polynomial perturbations realize exactly the strict function perturbations. -/
theorem card_strictPatterns_perturbPolynomials {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℝ) :
    (strictPatterns (fun j x => MvPolynomial.eval x (perturbPolynomials f j))).card =
      (strictPatterns (perturbFunctions (fun i x => MvPolynomial.eval x (f i)))).card := by
  classical
  let u : ((σ → ℝ) × ℝ) → (Option σ → ℝ) := fun x o => o.elim x.2 x.1
  have hu : Function.Surjective u := by
    intro x
    refine ⟨(fun i => x (some i), x none), ?_⟩
    funext o
    cases o <;> rfl
  have he : (fun j x => MvPolynomial.eval (u x) (perturbPolynomials f j)) =
      perturbFunctions (fun i x => MvPolynomial.eval x (f i)) := by
    funext j x
    exact eval_perturbPolynomials f x.1 x.2 j
  have h := strictPatterns_comp_domain
    (fun j x => MvPolynomial.eval x (perturbPolynomials f j)) u hu
  rw [he] at h
  exact (congrArg Finset.card h).symm

/-- The complete ternary sign estimate, conditional only on the stated Warren input. -/
theorem card_ternaryPatterns_le_of_warren {ι σ : Type*} [Fintype ι] [Fintype σ]
    (hW : WarrenStrictBound) (k : ℕ) (hk : 0 < k)
    (hN : Fintype.card σ + 1 ≤ 2 * Fintype.card ι)
    (f : ι → MvPolynomial σ ℝ) (hf : ∀ i, (f i).totalDegree ≤ k) :
    ((ternaryPatterns (fun i x => MvPolynomial.eval x (f i))).card : ℝ) ≤
      (8 * Real.exp 1 * k * Fintype.card ι / (Fintype.card σ + 1)) ^
        (Fintype.card σ + 1) := by
  classical
  have h := card_strictPatterns_le_of_warren hW k
    (by simp : 0 < Fintype.card (Option σ)) hk
    (by simpa [Nat.mul_comm] using hN : Fintype.card (Option σ) ≤ Fintype.card (ι × Bool))
    (perturbPolynomials f) (totalDegree_perturbPolynomials_le f k hk hf)
  have hc := card_ternaryPatterns_le_strictPatterns_perturb
    (fun i x => MvPolynomial.eval x (f i))
  rw [← card_strictPatterns_perturbPolynomials f] at hc
  refine (Nat.cast_le.mpr hc).trans (h.trans_eq ?_)
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.DirectSignCount` -/


/-!
# Direct polynomial sign counting

One common barrier has a positive local maximum for each realized strict
sign word. Distinct words give distinct maxima, whose pure-power critical
equations were counted algebraically. No hypersurface bound is assumed.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Finitely many nonzero evaluations admit one common positive barrier parameter. -/
theorem exists_common_positive_barrier {σ τ : Type*} [Fintype σ] [Fintype τ]
    (P : MvPolynomial σ ℝ) (d : ℕ) (a : τ → σ → ℝ)
    (ha : ∀ s, MvPolynomial.eval (a s) P ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s, 0 < MvPolynomial.eval (a s) (polynomialBarrier P d ε) := by
  let B (s : τ) := 1 + ∑ j, a s j ^ (2 * d + 2)
  have hB (s : τ) : 0 < B s := by
    have hs : 0 ≤ ∑ j, a s j ^ (2 * d + 2) :=
      Finset.sum_nonneg fun j _ => barrierPower_nonneg d (a s j)
    dsimp [B]
    linarith
  let v (s : τ) := MvPolynomial.eval (a s) P ^ 2 / B s
  have hv (s : τ) : 0 < v s := div_pos (sq_pos_of_ne_zero (ha s)) (hB s)
  obtain ⟨ε, hε, he⟩ := exists_positive_margin v
  refine ⟨ε, hε, fun s => ?_⟩
  have hs := he s (ne_of_gt (hv s))
  rw [abs_of_pos (hv s)] at hs
  have hb := (lt_div_iff₀ (hB s)).mp hs
  rw [eval_polynomialBarrier]
  exact sub_pos.mpr hb

/-- The direct strict-sign bound for every finite family, including empty index types. -/
theorem card_strictPatterns_le_direct {ι σ : Type*} [Fintype ι] [Fintype σ]
    (k : ℕ) (f : ι → MvPolynomial σ ℝ) (hf : ∀ i, (f i).totalDegree ≤ k) :
    (strictPatterns (fun i x => MvPolynomial.eval x (f i))).card ≤
      (2 * k * Fintype.card ι + 1) ^ Fintype.card σ := by
  classical
  let W := ↥(strictPatterns (fun i x => MvPolynomial.eval x (f i)))
  have hw (s : W) : ∃ x, ∀ i, if s.val i then 0 < MvPolynomial.eval x (f i)
      else MvPolynomial.eval x (f i) < 0 := by
    simpa [strictPatterns] using s.property
  choose a ha using hw
  let P := ∏ i, f i
  let d := k * Fintype.card ι
  have hP : P.totalDegree ≤ d := by
    calc
      _ ≤ ∑ i, (f i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ _i : ι, k := Finset.sum_le_sum (fun i _ => hf i)
      _ = _ := by simp [d, Nat.mul_comm]
  have hane (s : W) : MvPolynomial.eval (a s) P ≠ 0 := by
    simp only [P, map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hi := ha s i
    cases hsi : s.val i <;> simp only [hsi, Bool.false_eq_true, ite_false, ite_true] at hi
    · exact ne_of_lt hi
    · exact ne_of_gt hi
  obtain ⟨ε, hε, he⟩ := exists_common_positive_barrier P d a hane
  have hmax (s : W) : ∃ b : σ → ℝ,
      (∀ i, if s.val i then 0 < MvPolynomial.eval b (f i) else MvPolynomial.eval b (f i) < 0) ∧
      IsLocalMax (fun x => MvPolynomial.eval x (polynomialBarrier P d ε)) b :=
    exists_barrier_localMax_with_signs f s.val d hP ε hε (a s) (ha s) (he s)
  choose b hb hm using hmax
  have hinj : Function.Injective b := by
    intro s t h
    apply Subtype.ext
    funext i
    have hs := hb s i
    have ht := hb t i
    rw [h] at hs
    cases hs' : s.val i <;> cases ht' : t.val i <;> simp_all <;> linarith
  have hc := card_barrier_localMax_le P d hP ε hε b hinj hm
  simpa [W, d, Nat.mul_assoc] using hc

/-- Ternary words cost one extra variable and twice as many polynomials. -/
theorem card_ternaryPatterns_le_direct {ι σ : Type*} [Fintype ι] [Fintype σ]
    (k : ℕ) (hk : 1 ≤ k) (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ k) :
    (ternaryPatterns (fun i x => MvPolynomial.eval x (f i))).card ≤
      (4 * k * Fintype.card ι + 1) ^ (Fintype.card σ + 1) := by
  have h := card_strictPatterns_le_direct k (perturbPolynomials f)
    (totalDegree_perturbPolynomials_le f k hk hf)
  have hc := card_ternaryPatterns_le_strictPatterns_perturb
    (fun i x => MvPolynomial.eval x (f i))
  rw [← card_strictPatterns_perturbPolynomials f] at hc
  refine hc.trans (h.trans_eq ?_)
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
  congr 1
  ring

/-- The direct bound is stronger than the already verified coarse numerical budget. -/
theorem card_ternaryPatterns_le_coarse_direct {ι σ : Type*} [Fintype ι] [Fintype σ]
    (k : ℕ) (hk : 1 ≤ k) (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ k) :
    (ternaryPatterns (fun i x => MvPolynomial.eval x (f i))).card ≤
      (4 * k * Fintype.card ι + 2) ^ (Fintype.card σ + 2) := by
  apply (card_ternaryPatterns_le_direct k hk f hf).trans
  exact (Nat.pow_le_pow_left (by omega) _).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.Basic` -/


/-!
# Finite additive arrays and convex labels

These definitions implement the array-counting setup in section 1 of the
VCₙ argument in `FCreportv1.html`, exploration 30. The VCₙ predicate itself
is imported from the pinned Formal Conjectures library, not redefined here.
-/

namespace VCDimConvexBound

abbrev Grid (D m : ℕ) := Fin D → Fin m

abbrev Point (D : ℕ) := Fin D → ℝ

/-- The point associated with an index of an additive array. -/
def gridSum {D m : ℕ} {G : Type*} [AddCommMonoid G]
    (z : Fin D → Fin m → G) (i : Grid D m) : G :=
  ∑ k, z k (i k)

/-- A label set is realized by one additive array in a fixed set `C`. -/
def Realizes {D m : ℕ} {G : Type*} [AddCommMonoid G]
    (C : Set G) (S : Set (Grid D m)) : Prop :=
  ∃ z : Fin D → Fin m → G, ∀ i, gridSum z i ∈ C ↔ i ∈ S

/-- All labels realized by convex sets and additive arrays in ambient dimension `D`. -/
noncomputable def convexLabels (D m : ℕ) : Finset (Set (Grid D m)) := by
  classical
  exact Finset.univ.filter fun S =>
    ∃ C : Set (Point D), Convex ℝ C ∧ Realizes C S

@[simp] theorem mem_convexLabels {D m : ℕ} {S : Set (Grid D m)} :
    S ∈ convexLabels D m ↔ ∃ C : Set (Point D), Convex ℝ C ∧ Realizes C S := by
  classical
  simp [convexLabels]

@[simp] theorem card_grid (D m : ℕ) : Fintype.card (Grid D m) = m ^ D := by
  simp [Grid]

@[simp] theorem card_label_sets (D m : ℕ) :
    Fintype.card (Set (Grid D m)) = 2 ^ (m ^ D) := by
  simp

/-- The explicit bound proposed in the paper argument. -/
def bound (n : ℕ) : ℕ := 2 ^ (8 * (n + 2) ^ n) - 1

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HullEncoding` -/


/-!
# Recover convex labels from an irredundant finite set

This implements the finite convex-hull reduction in section 4 of the paper
argument. Minimality removes redundant indices, including repeated points.
The ambient convex set need not be closed or bounded. No estimate on the
number of representatives is asserted here.
-/

namespace VCDimConvexBound

variable {ι : Type*} {D : ℕ}

/-- The convex hull of the points indexed by a finite set. -/
def indexedHull (q : ι → Point D) (V : Finset ι) : Set (Point D) :=
  convexHull ℝ (q '' (V : Set ι))

/-- No selected point is in the convex hull of the other selected indices. -/
def ConvexIndependentOn [DecidableEq ι] (q : ι → Point D) (V : Finset ι) : Prop :=
  ∀ i ∈ V, q i ∉ indexedHull q (V.erase i)

theorem indexedHull_mono (q : ι → Point D) {V W : Finset ι} (h : V ⊆ W) :
    indexedHull q V ⊆ indexedHull q W :=
  convexHull_mono (Set.image_mono h)

theorem mem_indexedHull (q : ι → Point D) {V : Finset ι} {i : ι} (hi : i ∈ V) :
    q i ∈ indexedHull q V :=
  subset_convexHull ℝ _ ⟨i, hi, rfl⟩

/-- Removing a redundant index does not change the hull. -/
theorem indexedHull_erase_eq [DecidableEq ι] (q : ι → Point D) (V : Finset ι) (i : ι)
    (hi : q i ∈ indexedHull q (V.erase i)) :
    indexedHull q (V.erase i) = indexedHull q V := by
  apply Set.Subset.antisymm (indexedHull_mono q (Finset.erase_subset _ _))
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨j, hj, rfl⟩
  by_cases hji : j = i
  · subst j
    exact hi
  · exact mem_indexedHull q (Finset.mem_erase.mpr ⟨hji, hj⟩)

/-- A smallest subset of `E` with the same hull exists, including when `E` is empty. -/
theorem exists_minimal_generators (q : ι → Point D) (E : Finset ι) :
    ∃ V : Finset ι, V ⊆ E ∧ indexedHull q V = indexedHull q E ∧
      ∀ W : Finset ι, W ⊆ E → indexedHull q W = indexedHull q E → V.card ≤ W.card := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ V : Finset ι, V ⊆ E ∧ indexedHull q V = indexedHull q E ∧ V.card = k
  have hex : ∃ k, P k := ⟨E.card, E, Finset.Subset.refl E, rfl, rfl⟩
  obtain ⟨V, hVE, hHull, hcard⟩ := Nat.find_spec hex
  refine ⟨V, hVE, hHull, ?_⟩
  intro W hWE hW
  rw [hcard]
  exact Nat.find_min' hex ⟨W, hWE, hW, rfl⟩

/-- Minimal generators are convex independent as an indexed family. -/
theorem exists_convexIndependent_generators [DecidableEq ι] (q : ι → Point D) (E : Finset ι) :
    ∃ V : Finset ι, V ⊆ E ∧ indexedHull q V = indexedHull q E ∧
      ConvexIndependentOn q V := by
  obtain ⟨V, hVE, hHull, hmin⟩ := exists_minimal_generators q E
  refine ⟨V, hVE, hHull, ?_⟩
  intro i hi hredundant
  have hle := hmin (V.erase i) ((Finset.erase_subset _ _).trans hVE)
    ((indexedHull_erase_eq q V i hredundant).trans hHull)
  exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hi)) hle

/-- Connect the finite erase formulation to mathlib's standard predicate. -/
theorem ConvexIndependentOn.convexIndependent [DecidableEq ι]
    {q : ι → Point D} {V : Finset ι} (hV : ConvexIndependentOn q V) :
    ConvexIndependent ℝ (fun i : V => q i) := by
  intro s i hi
  by_contra his
  apply hV i i.property
  apply convexHull_mono _ hi
  rintro _ ⟨j, hjs, rfl⟩
  refine ⟨j.val, Finset.mem_erase.mpr ⟨?_, j.property⟩, rfl⟩
  intro hji
  have h : j = i := Subtype.ext hji
  exact his (h ▸ hjs)

/-- Convex independence of an indexed family excludes repeated points. -/
theorem ConvexIndependentOn.injOn [DecidableEq ι] {q : ι → Point D} {V : Finset ι}
    (hV : ConvexIndependentOn q V) : Set.InjOn q (V : Set ι) := by
  intro i hi j hj hij
  by_contra hne
  apply hV i hi
  rw [hij]
  exact mem_indexedHull q (Finset.mem_erase.mpr ⟨Ne.symm hne, hj⟩)

/-- The positive indices of a finite configuration. -/
noncomputable def positiveIndices [Fintype ι] (q : ι → Point D) (C : Set (Point D)) :
    Finset ι := by
  classical
  exact Finset.univ.filter fun i => q i ∈ C

@[simp] theorem mem_positiveIndices [Fintype ι] (q : ι → Point D)
    (C : Set (Point D)) (i : ι) : i ∈ positiveIndices q C ↔ q i ∈ C := by
  classical
  simp [positiveIndices]

/-- Taking the hull of all positive points preserves the label of every indexed point. -/
theorem mem_indexedHull_positive_iff [Fintype ι] (q : ι → Point D)
    (C : Set (Point D)) (hC : Convex ℝ C) (i : ι) :
    q i ∈ indexedHull q (positiveIndices q C) ↔ q i ∈ C := by
  constructor
  · apply convexHull_min _ hC
    rintro _ ⟨j, hj, rfl⟩
    exact (mem_positiveIndices q C j).mp hj
  · intro hi
    exact mem_indexedHull q ((mem_positiveIndices q C i).mpr hi)

/-- Every convex label has distinct, convex-independent representatives.
The later geometric argument must supply a bound on `V.card`. -/
theorem exists_label_generators [DecidableEq ι] [Fintype ι] (q : ι → Point D)
    (C : Set (Point D)) (hC : Convex ℝ C) :
    ∃ V : Finset ι, V ⊆ positiveIndices q C ∧ ConvexIndependentOn q V ∧
      Set.InjOn q (V : Set ι) ∧ ∀ i, q i ∈ C ↔ q i ∈ indexedHull q V := by
  obtain ⟨V, hVE, hHull, hind⟩ :=
    exists_convexIndependent_generators q (positiveIndices q C)
  refine ⟨V, hVE, hind, hind.injOn, ?_⟩
  intro i
  rw [hHull]
  exact (mem_indexedHull_positive_iff q C hC i).symm

/-- Connect the finite-hull reduction to the label sets counted in `Basic`.
There is no bound on `V.card` yet. -/
theorem exists_hull_encoding_of_mem_convexLabels {m : ℕ} {S : Set (Grid D m)}
    (hS : S ∈ convexLabels D m) :
    ∃ (z : Fin D → Fin m → Point D) (V : Finset (Grid D m)),
      ConvexIndependentOn (gridSum z) V ∧
      ConvexIndependent ℝ (fun i : V => gridSum z i) ∧
      Set.InjOn (gridSum z) (V : Set (Grid D m)) ∧
      (V : Set (Grid D m)) ⊆ S ∧
      S = {i | gridSum z i ∈ indexedHull (gridSum z) V} := by
  classical
  obtain ⟨C, hC, z, hz⟩ := mem_convexLabels.mp hS
  obtain ⟨V, hVE, hind, hinj, hlabels⟩ := exists_label_generators (gridSum z) C hC
  refine ⟨z, V, hind, hind.convexIndependent, hinj, ?_, ?_⟩
  · intro i hi
    exact (hz i).mp ((mem_positiveIndices (gridSum z) C i).mp (hVE hi))
  · ext i
    exact (hz i).symm.trans (hlabels i)

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.ConvexCertificates` -/


/-!
# Finite convex membership certificates in homogeneous coordinates

The extra coordinate is one. Convex membership becomes a nonnegative linear
system, and Caratheodory supplies a positive certificate with independent
columns and at most `D + 1` points. Original indices are retained, even when
the configuration has repeated points or lies in a proper affine subspace.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Homogeneous coordinates: the constant coordinate is indexed by `none`. -/
def augmentedPoint {D : ℕ} (x : Point D) : Option (Fin D) → ℝ := fun r => r.elim 1 x

theorem sum_smul_augmentedPoint_eq_iff {ι : Type*} [Fintype ι] {D : ℕ}
    (q : ι → Point D) (w : ι → ℝ) (x : Point D) :
    (∑ i, w i • augmentedPoint (q i)) = augmentedPoint x ↔
      (∑ i, w i = 1) ∧ (∑ i, w i • q i = x) := by
  constructor
  · intro h
    constructor
    · simpa [augmentedPoint, Finset.sum_apply] using congrFun h none
    · funext a
      simpa [augmentedPoint, Finset.sum_apply] using congrFun h (some a)
  · rintro ⟨hw, hx⟩
    funext r
    cases r with
    | none => simpa [augmentedPoint, Finset.sum_apply] using hw
    | some a => simpa [augmentedPoint, Finset.sum_apply] using congrFun hx a

/-- Affine independence is exactly linear independence after homogenization. -/
theorem affineIndependent_iff_augmentedPoint {ι : Type*} {D : ℕ} (q : ι → Point D) :
    AffineIndependent ℝ q ↔ LinearIndependent ℝ (fun i => augmentedPoint (q i)) := by
  rw [affineIndependent_iff, linearIndependent_iff']
  constructor
  · intro h s w hw
    apply h s w
    · simpa [augmentedPoint, Finset.sum_apply] using congrFun hw none
    · funext a
      simpa [augmentedPoint, Finset.sum_apply] using congrFun hw (some a)
  · intro h s w hw hx
    apply h s w
    funext r
    cases r with
    | none => simpa [augmentedPoint, Finset.sum_apply] using hw
    | some a => simpa [augmentedPoint, Finset.sum_apply] using congrFun hx a

/-- A fixed finite family suffices for the weights, including zero weights. -/
theorem mem_convexHull_range_iff_weights {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) (x : E) :
    x ∈ convexHull ℝ (Set.range q) ↔
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • q i = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, w, hw, hsum, hx⟩ := hx
    refine ⟨fun i => if i ∈ s then w i else 0, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with hi
      · exact hw i hi
      · exact le_rfl
    · simpa using hsum
    · simpa [Finset.affineCombination_eq_linear_combination s q w hsum,
        ite_smul] using hx
  · rintro ⟨w, hw, hsum, hx⟩
    exact mem_convexHull_of_exists_fintype w q hw hsum (Set.mem_range_self) hx

/-- Convex membership is a linear system with nonnegative coefficients. -/
theorem mem_convexHull_range_iff_augmented {ι : Type*} [Fintype ι] {D : ℕ}
    (q : ι → Point D) (x : Point D) :
    x ∈ convexHull ℝ (Set.range q) ↔
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧
        ∑ i, w i • augmentedPoint (q i) = augmentedPoint x := by
  simp only [sum_smul_augmentedPoint_eq_iff, mem_convexHull_range_iff_weights]

/-- A positive, linearly independent certificate using only the original allowed indices. -/
theorem exists_independent_convexCertificate {ι : Type*} {D : ℕ}
    (q : ι → Point D) (V : Finset ι) {x : Point D} (hx : x ∈ indexedHull q V) :
    ∃ (r : ℕ) (c : Fin r → ι) (w : Fin r → ℝ),
      0 < r ∧ r ≤ D + 1 ∧ (∀ i, c i ∈ V) ∧ Function.Injective c ∧
      LinearIndependent ℝ (fun i => augmentedPoint (q (c i))) ∧
      (∀ i, 0 < w i) ∧ ∑ i, w i • augmentedPoint (q (c i)) = augmentedPoint x := by
  classical
  obtain ⟨κ, _, z, w, hz, hi, hw, hsum, hx⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  choose c hcV hcq using fun j => hz (Set.mem_range_self j)
  let e := (Fintype.equivFin κ).symm
  have ha : AffineIndependent ℝ (fun i : Fin (Fintype.card κ) => q (c (e i))) := by
    simpa only [hcq, Function.comp_def] using! hi.comp_embedding e.toEmbedding
  have hl := (affineIndependent_iff_augmentedPoint _).mp ha
  refine ⟨Fintype.card κ, c ∘ e, w ∘ e, ?_, ?_, ?_, ?_, hl, ?_, ?_⟩
  · by_contra! h
    have : IsEmpty κ := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    simp at hsum
  · simpa using hl.fintype_card_le_finrank
  · exact fun i => hcV (e i)
  · intro i j hij
    exact ha.injective (congrArg q hij)
  · exact fun i => hw (e i)
  · apply (sum_smul_augmentedPoint_eq_iff _ _ _).mpr
    constructor
    · exact (e.sum_comp w).trans hsum
    · simpa only [Function.comp_def, hcq] using
        (e.sum_comp (fun i => w i • z i)).trans hx

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.FiniteExposedFaces` -/


/-!
# Exposed faces of finite convex hulls

A nonpositive functional vanishes on a convex combination exactly when all
positive coefficients are supported on its zero set. This also proves that
such finite exposed faces intersect along the hull of their common vertices.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The zero level of a nonpositive functional commutes with finite convex hull. -/
theorem convexHull_inter_zero_level {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Set E) (hA : A.Finite) (f : E →ₗ[ℝ] ℝ) (hf : ∀ x ∈ A, f x ≤ 0) :
    convexHull ℝ {x ∈ A | f x = 0} = {x ∈ convexHull ℝ A | f x = 0} := by
  classical
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro x hx
      exact ⟨subset_convexHull ℝ A hx.1, hx.2⟩
    · exact (convex_convexHull ℝ A).inter (convex_hyperplane ⟨f.map_add, f.map_smul⟩ 0)
  · rintro x ⟨hx, hfx⟩
    let : Fintype A := hA.fintype
    have hr : Set.range (fun y : A => (y : E)) = A := Subtype.range_coe
    rw [← hr, mem_convexHull_range_iff_weights] at hx
    obtain ⟨w, hw, hsum, hx⟩ := hx
    have hterms : ∀ y : A, w y * f y ≤ 0 :=
      fun y => mul_nonpos_of_nonneg_of_nonpos (hw y) (hf y y.property)
    have htotal : ∑ y : A, w y * f y = 0 := by
      simpa only [map_sum, map_smul, smul_eq_mul, hfx] using congrArg f hx
    have hzero : ∀ y : A, f y ≠ 0 → w y = 0 := by
      intro y hy
      exact (mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonpos
        (fun y _ => hterms y)).mp htotal y (Finset.mem_univ y))).resolve_right hy
    let good : Set A := {y | f y = 0}
    have hsum' : ∑ y : good, w y.val = 1 := by
      have h := Finset.sum_congr_set good w (fun y => w y.val)
        (by intros; rfl) (by intro y hy; exact hzero y hy)
      exact h.symm.trans hsum
    have hx' : ∑ y : good, w y.val • (y.val : E) = x := by
      have h := Finset.sum_congr_set good (fun y => w y • (y : E))
        (fun y => w y.val • (y.val : E)) (by intros; rfl)
        (by intro y hy; rw [hzero y hy, zero_smul])
      exact h.symm.trans hx
    exact mem_convexHull_of_exists_fintype (fun y : good => w y.val)
      (fun y : good => (y.val : E)) (fun y => hw y.val) hsum'
      (fun y => ⟨y.val.property, y.property⟩) hx'

/-- Exact zero/nonzero values on the generators identify the whole exposed face. -/
theorem convexHull_eq_zero_face {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A S : Set E) (hA : A.Finite) (hS : S ⊆ A) (f : E →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ A, f x ≤ 0) (hz : ∀ x ∈ A, f x = 0 ↔ x ∈ S) :
    convexHull ℝ S = {x ∈ convexHull ℝ A | f x = 0} := by
  have he : {x ∈ A | f x = 0} = S := by
    ext x
    exact ⟨fun h => (hz x h.1).mp h.2, fun h => ⟨hS h, (hz x (hS h)).mpr h⟩⟩
  simpa only [he] using convexHull_inter_zero_level A hA f hf

/-- This is a genuine exposed set in mathlib's sense, including the empty face. -/
theorem isExposed_convexHull_of_zero_face {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (A S : Set E) (hA : A.Finite) (hS : S ⊆ A)
    (f : E →L[ℝ] ℝ) (hf : ∀ x ∈ A, f x ≤ 0)
    (hz : ∀ x ∈ A, f x = 0 ↔ x ∈ S) :
    IsExposed ℝ (convexHull ℝ A) (convexHull ℝ S) := by
  have he := convexHull_eq_zero_face A S hA hS f.toLinearMap hf hz
  have hle : ∀ x ∈ convexHull ℝ A, f x ≤ 0 :=
    convexHull_min hf (convex_halfSpace_le ⟨f.map_add, f.map_smul⟩ 0)
  intro hn
  obtain ⟨w, hw⟩ := hn
  have hw' := he ▸ hw
  refine ⟨f, ?_⟩
  rw [he]
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact ⟨hx, fun y hy => hfx ▸ hle y hy⟩
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, le_antisymm (hle x hx) ?_⟩
    have hfw : f w = 0 := hw'.2
    simpa only [hfw] using! hmax w hw'.1

/-- The hull of an exposed selection meets any sub-hull precisely on common generators. -/
theorem convexHull_inter_convexHull_of_zero_face {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (A S T : Set E) (hA : A.Finite) (hS : S ⊆ A) (hT : T ⊆ A)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x ∈ A, f x ≤ 0)
    (hz : ∀ x ∈ A, f x = 0 ↔ x ∈ S) :
    convexHull ℝ S ∩ convexHull ℝ T = convexHull ℝ (S ∩ T) := by
  have heS := convexHull_eq_zero_face A S hA hS f hf hz
  have heT := convexHull_eq_zero_face T (S ∩ T) (hA.subset hT)
    Set.inter_subset_right f (fun x hx => hf x (hT hx))
    (fun x hx => by simp only [Set.mem_inter_iff, (hz x (hT hx)), hx, and_true])
  rw [heS, heT]
  ext x
  constructor
  · rintro ⟨⟨_, hfx⟩, hxT⟩
    exact ⟨hxT, hfx⟩
  · rintro ⟨hxT, hfx⟩
    exact ⟨⟨convexHull_mono hT hxT, hfx⟩, hxT⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.CenteredFaces` -/


/-!
# Centered combinations on disjoint exposed faces

A strictly negative value at the center lets supporting functionals compare
coefficient masses directly. No normalization, relative-interior theorem or
sphere homeomorphism is needed, and either coefficient family may be zero.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The average of an indexed finite family, retaining any repetitions. -/
noncomputable def finiteAverage {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) : E :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, q i

/-- Averaging a nonpositive functional with one negative value gives a negative value. -/
theorem map_finiteAverage_neg {ι E : Type*} [Fintype ι] [Nonempty ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) (f : E →ₗ[ℝ] ℝ)
    (hf : ∀ i, f (q i) ≤ 0) (hlt : ∃ i, f (q i) < 0) :
    f (finiteAverage q) < 0 := by
  have hs : ∑ i, f (q i) < 0 := by
    obtain ⟨i, hi⟩ := hlt
    simpa using Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hf j)
      ⟨i, Finset.mem_univ i, hi⟩
  have hc : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  simpa only [finiteAverage, map_smul, map_sum, smul_eq_mul] using
    mul_neg_of_pos_of_neg (inv_pos.mpr hc) hs

/-- A weighted combination after translating all generators by the same center. -/
noncomputable def centeredCombination {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) (c : E) (a : ι → ℝ) : E :=
  ∑ i, a i • (q i - c)

/-- Applying a functional separates the uncentered sum from the coefficient mass. -/
theorem map_centeredCombination {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) (c : E) (a : ι → ℝ)
    (f : E →ₗ[ℝ] ℝ) :
    f (centeredCombination q c a) =
      (∑ i, a i * f (q i)) - (∑ i, a i) * f c := by
  simp [centeredCombination, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

/-- A supporting functional compares the masses of equal centered combinations. -/
theorem sum_le_of_centeredCombination_eq {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) (c : E) (a b : ι → ℝ)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ i, f (q i) ≤ 0) (hc : f c < 0)
    (ha : ∀ i, a i ≠ 0 → f (q i) = 0) (hb : ∀ i, 0 ≤ b i)
    (heq : centeredCombination q c a = centeredCombination q c b) :
    ∑ i, a i ≤ ∑ i, b i := by
  have hzero : ∑ i, a i * f (q i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : a i = 0
    · simp [h]
    · simp [ha i h]
  have hnonpos : ∑ i, b i * f (q i) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hb i) (hf i))
  have h := congrArg f heq
  rw [map_centeredCombination, map_centeredCombination, hzero] at h
  exact (mul_le_mul_right_of_neg hc).mp (by linarith :
    (∑ i, b i) * f c ≤ (∑ i, a i) * f c)

/-- Disjoint supported nonnegative combinations with positive total mass cannot coincide.
The first functional is strict on the second support. Zero coefficient families
are included; no division by their masses is used. -/
theorem centeredCombination_sub_ne_zero {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (q : ι → E) (c : E) (a b : ι → ℝ)
    (f g : E →ₗ[ℝ] ℝ)
    (hf : ∀ i, f (q i) ≤ 0) (hg : ∀ i, g (q i) ≤ 0)
    (hfc : f c < 0) (hgc : g c < 0)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hfa : ∀ i, a i ≠ 0 → f (q i) = 0)
    (hgb : ∀ i, b i ≠ 0 → g (q i) = 0)
    (hfb : ∀ i, b i ≠ 0 → f (q i) < 0)
    (hmass : 0 < (∑ i, a i) + ∑ i, b i) :
    centeredCombination q c a - centeredCombination q c b ≠ 0 := by
  intro hzero
  have heq := sub_eq_zero.mp hzero
  have hab := sum_le_of_centeredCombination_eq q c a b f hf hfc hfa hb heq
  have hba := sum_le_of_centeredCombination_eq q c b a g hg hgc hgb ha heq.symm
  have hm : (∑ i, a i) = ∑ i, b i := le_antisymm hab hba
  have hsumA : ∑ i, a i * f (q i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : a i = 0
    · simp [h]
    · simp [hfa i h]
  have h := congrArg f heq
  rw [map_centeredCombination, map_centeredCombination, hsumA, hm] at h
  have hsumB : ∑ i, b i * f (q i) = 0 := by linarith
  have hbzero : ∀ i, b i = 0 := by
    intro i
    by_contra hn
    have hz := (Finset.sum_eq_zero_iff_of_nonpos
      (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hb j) (hf j))).mp hsumB
      i (Finset.mem_univ i)
    exact (ne_of_lt (mul_neg_of_pos_of_neg (lt_of_le_of_ne (hb i) (Ne.symm hn))
      (hfb i hn))) hz
  simp only [hbzero, Finset.sum_const_zero] at hm hmass
  linarith

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.BinomialAverage` -/


/-!
# A lower bound for an average of binomial coefficients

We use Jensen for the ordinary power function on nonnegative reals and
`Nat.pow_sub_le_descFactorial`. This avoids defining binomial coefficients
at real arguments. The loss of `s` in the average degree is sufficient for
the dense-fiber estimate under the assumption `δ * m ≥ 2 * s`.
-/

namespace VCDimConvexBound

open Finset

variable {β : Type*} [Fintype β] [Nonempty β]

/-- Jensen's inequality with uniform weights. -/
theorem power_mean_le (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) (s : ℕ) :
    ((∑ b, f b) / (Fintype.card β : ℝ)) ^ s ≤
      (∑ b, f b ^ s) / (Fintype.card β : ℝ) := by
  have hB : 0 < (Fintype.card β : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∑ _b : β, (Fintype.card β : ℝ)⁻¹ = 1 := by
    simp [hB.ne']
  have h := (convexOn_pow (𝕜 := ℝ) s).map_sum_le (t := univ)
    (w := fun _ : β => (Fintype.card β : ℝ)⁻¹) (p := f)
    (fun _ _ => inv_nonneg.mpr hB.le) hw (fun b _ => hf b)
  simp only [smul_eq_mul, ← mul_sum] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- If the average degree is at least `a + s`, its average binomial coefficient
is at least `a^s / s!`, stated without division by the factorial. -/
theorem power_le_factorial_mul_average_choose (d : β → ℕ) (s : ℕ) (a : ℝ)
    (ha : 0 ≤ a)
    (havg : a + s ≤ (∑ b, (d b : ℝ)) / (Fintype.card β : ℝ)) :
    a ^ s ≤ (s.factorial : ℝ) * (∑ b, ((d b).choose s : ℝ)) /
      (Fintype.card β : ℝ) := by
  let x : β → ℝ := fun b => (d b + 1 - s : ℕ)
  have hB : 0 < (Fintype.card β : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hx : ∀ b, 0 ≤ x b := fun _ => Nat.cast_nonneg _
  have hd : ∀ b, (d b : ℝ) ≤ x b + s := by
    intro b
    dsimp [x]
    exact_mod_cast (show d b ≤ (d b + 1 - s) + s by omega)
  have hsum : (∑ b, (d b : ℝ)) ≤
      (∑ b, x b) + (Fintype.card β : ℝ) * s := by
    simpa only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] using
      sum_le_sum (fun b (_ : b ∈ (univ : Finset β)) => hd b)
  have havg' := (le_div_iff₀ hB).mp havg
  have hax : a ≤ (∑ b, x b) / (Fintype.card β : ℝ) := by
    apply (le_div_iff₀ hB).mpr
    nlinarith
  have hchoose : ∀ b, x b ^ s ≤ (s.factorial : ℝ) * ((d b).choose s : ℝ) := by
    intro b
    have h := Nat.pow_sub_le_descFactorial (d b) s
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    dsimp [x]
    exact_mod_cast h
  calc
    a ^ s ≤ ((∑ b, x b) / (Fintype.card β : ℝ)) ^ s := pow_le_pow_left₀ ha hax s
    _ ≤ (∑ b, x b ^ s) / (Fintype.card β : ℝ) := power_mean_le x hx s
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hB.le
      simpa only [mul_sum] using
        sum_le_sum (fun b (_ : b ∈ (univ : Finset β)) => hchoose b)

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.DenseFiber` -/


/-!
# Common fibers of a dense finite relation

The first step of the dense-box argument counts pairs `(A, b)`, where `A`
has `s` elements and every `a ∈ A` is related to `b`.
-/

namespace VCDimConvexBound
namespace DenseFiber

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
variable (R : α → β → Prop) [DecidableRel R]

/-- The left fiber over a right vertex. -/
def fiber (b : β) : Finset α := univ.filter fun a => R a b

/-- The right vertices related to every member of `A`. -/
def common (A : Finset α) : Finset β := univ.filter fun b => ∀ a ∈ A, R a b

omit [Fintype β] [DecidableEq α] in
@[simp] theorem mem_fiber (a : α) (b : β) : a ∈ fiber R b ↔ R a b := by
  simp [fiber]

@[simp] theorem mem_common (A : Finset α) (b : β) :
    b ∈ common R A ↔ ∀ a ∈ A, R a b := by
  simp [common]

omit [Fintype β] in
theorem powersetCard_fiber (s : ℕ) (b : β) :
    (fiber R b).powersetCard s =
      (univ.powersetCard s).filter (fun A : Finset α => ∀ a ∈ A, R a b) := by
  ext A
  simp only [mem_powersetCard, mem_filter, subset_univ, true_and]
  have h : A ⊆ fiber R b ↔ ∀ a ∈ A, R a b := by simp [subset_iff]
  rw [h]
  exact and_comm

/-- Count complete stars by the right vertex or by their left vertex set. -/
theorem sum_choose_eq_sum_common (s : ℕ) :
    ∑ b : β, (fiber R b).card.choose s =
      ∑ A ∈ (univ : Finset α).powersetCard s, (common R A).card := by
  simp_rw [← card_powersetCard, powersetCard_fiber, common, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- One common fiber is at least the average, in an integer form without division. -/
theorem exists_common_ge_average (s : ℕ) (hs : s ≤ Fintype.card α) :
    ∃ A : Finset α, A.card = s ∧
      (∑ b : β, (fiber R b).card.choose s) ≤
        (Fintype.card α).choose s * (common R A).card := by
  have hne : ((univ : Finset α).powersetCard s).Nonempty := by
    apply card_pos.mp
    simpa only [card_powersetCard, card_univ] using Nat.choose_pos hs
  obtain ⟨A, hA, hmax⟩ :=
    ((univ : Finset α).powersetCard s).exists_max_image (fun A => (common R A).card) hne
  refine ⟨A, (mem_powersetCard.mp hA).2, ?_⟩
  rw [sum_choose_eq_sum_common]
  calc
    _ ≤ ∑ _B ∈ (univ : Finset α).powersetCard s, (common R A).card :=
      sum_le_sum hmax
    _ = _ := by simp

/-- A dense relation contains an `s`-element left set with a common fiber of
density at least `(δ / 2)^s`, with no unproved analytic or counting input. -/
theorem exists_common_of_density [Nonempty α] [Nonempty β]
    (s : ℕ) (hs : s ≤ Fintype.card α) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlarge : 2 * (s : ℝ) ≤ δ * Fintype.card α)
    (hdensity : δ * (Fintype.card α : ℝ) * Fintype.card β ≤
      ∑ b : β, ((fiber R b).card : ℝ)) :
    ∃ A : Finset α, A.card = s ∧
      (δ / 2) ^ s * (Fintype.card β : ℝ) ≤ (common R A).card := by
  obtain ⟨A, hA, havg⟩ := exists_common_ge_average R s hs
  refine ⟨A, hA, ?_⟩
  have hM : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hB : 0 < (Fintype.card β : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hpow := power_le_factorial_mul_average_choose
    (fun b => (fiber R b).card) s (δ * Fintype.card α / 2)
    (by positivity) (by
      apply (le_div_iff₀ hB).mpr
      calc
        _ ≤ δ * (Fintype.card α : ℝ) * Fintype.card β :=
          mul_le_mul_of_nonneg_right (by linarith) hB.le
        _ ≤ _ := hdensity)
  have havgR : (∑ b : β, ((fiber R b).card.choose s : ℝ)) ≤
      ((Fintype.card α).choose s : ℝ) * (common R A).card := by
    exact_mod_cast havg
  have hfactor : (s.factorial : ℝ) * ((Fintype.card α).choose s : ℝ) ≤
      (Fintype.card α : ℝ) ^ s := by
    have h := Nat.descFactorial_le_pow (Fintype.card α) s
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast h
  have htotal : (δ * Fintype.card α / 2) ^ s * (Fintype.card β : ℝ) ≤
      (Fintype.card α : ℝ) ^ s * (common R A).card := by
    calc
      _ ≤ (s.factorial : ℝ) * ∑ b : β, ((fiber R b).card.choose s : ℝ) :=
        (le_div_iff₀ hB).mp hpow
      _ ≤ (s.factorial : ℝ) *
          (((Fintype.card α).choose s : ℝ) * (common R A).card) :=
        mul_le_mul_of_nonneg_left havgR (Nat.cast_nonneg _)
      _ = ((s.factorial : ℝ) * (Fintype.card α).choose s) * (common R A).card :=
        (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _)
  apply (mul_le_mul_iff_right₀ (pow_pos hM s)).mp
  calc
    (Fintype.card α : ℝ) ^ s * ((δ / 2) ^ s * Fintype.card β) =
        (δ * Fintype.card α / 2) ^ s * (Fintype.card β : ℝ) := by
      rw [show δ * (Fintype.card α : ℝ) / 2 = (Fintype.card α : ℝ) * (δ / 2) by ring,
        mul_pow]
      ring
    _ ≤ _ := htotal

end DenseFiber
end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.DenseBox` -/


/-!
# Iterating common fibers to produce a complete box

Every coordinate of a box has the same prescribed size. The density is
updated by `δ ↦ (δ / 2)^s` at each step.
-/

namespace VCDimConvexBound

open Finset

/-- An `s × ⋯ × s` box of indices contained in `E`. -/
def ContainsBox {k m : ℕ} (E : Finset (Grid k m)) (s : ℕ) : Prop :=
  ∃ A : Fin k → Finset (Fin m), (∀ j, (A j).card = s) ∧
    ∀ i : Grid k m, (∀ j, i j ∈ A j) → i ∈ E

/-- The density after successively selecting common fibers. -/
noncomputable def densityIter (s : ℕ) (δ : ℝ) : ℕ → ℝ
  | 0 => δ
  | j + 1 => (densityIter s δ j / 2) ^ s

theorem densityIter_shift (s : ℕ) (δ : ℝ) (j : ℕ) :
    densityIter s δ (j + 1) = densityIter s ((δ / 2) ^ s) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (densityIter s δ (j + 1) / 2) ^ s =
      (densityIter s ((δ / 2) ^ s) j / 2) ^ s
    rw [ih]

/-- The first coordinate and the remaining coordinates form a product. -/
def consEquiv (k m : ℕ) : Fin m × Grid k m ≃ Grid (k + 1) m where
  toFun p := Fin.cons p.1 p.2
  invFun i := (i 0, Fin.tail i)
  left_inv p := by rcases p with ⟨a, i⟩; simp
  right_inv i := Fin.cons_self_tail i

/-- Partition the points of `E` by their remaining coordinates. -/
theorem sum_card_cons_fiber {k m : ℕ} (E : Finset (Grid (k + 1) m)) :
    ∑ b : Grid k m, (DenseFiber.fiber (fun a b => Fin.cons a b ∈ E) b).card =
      E.card := by
  classical
  have h := (consEquiv k m).sum_comp (fun i => if i ∈ E then (1 : ℕ) else 0)
  change (∑ p : Fin m × Grid k m, if Fin.cons p.1 p.2 ∈ E then (1 : ℕ) else 0) =
    ∑ i : Grid (k + 1) m, if i ∈ E then 1 else 0 at h
  rw [Fintype.sum_prod_type] at h
  calc
    _ = ∑ b : Grid k m, ∑ a : Fin m, if Fin.cons a b ∈ E then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro b _
      rw [DenseFiber.fiber, card_eq_sum_ones, sum_filter]
    _ = ∑ a : Fin m, ∑ b : Grid k m, if Fin.cons a b ∈ E then (1 : ℕ) else 0 := sum_comm
    _ = ∑ i : Grid (k + 1) m, if i ∈ E then 1 else 0 := h
    _ = _ := by simp

/-- A complete box follows whenever all intermediate densities permit another step. -/
theorem containsBox_of_density (k m s : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (E : Finset (Grid k m))
    (hdensity : δ * (m : ℝ) ^ k ≤ E.card)
    (hsteps : ∀ j < k, 2 * (s : ℝ) ≤ densityIter s δ j * m) : ContainsBox E s := by
  classical
  induction k generalizing δ with
  | zero =>
    have hpos : 0 < E.card := by
      have hreal : 0 < (E.card : ℝ) :=
        lt_of_lt_of_le hδ (by simpa only [pow_zero, mul_one] using hdensity)
      exact_mod_cast hreal
    obtain ⟨i, hi⟩ := card_pos.mp hpos
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro j _
      simpa only [Subsingleton.elim j i] using hi
  | succ k ih =>
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let R : Fin m → Grid k m → Prop := fun a b => Fin.cons a b ∈ E
    have hlarge : 2 * (s : ℝ) ≤ δ * m := hsteps 0 (Nat.zero_lt_succ k)
    have hs : s ≤ Fintype.card (Fin m) := by
      simp only [Fintype.card_fin]
      have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have hprod : δ * m ≤ (m : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ1 hmR
      have hsR : (s : ℝ) ≤ m := calc
        (s : ℝ) ≤ 2 * s := by nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
        _ ≤ δ * m := hlarge
        _ ≤ m := hprod
      exact_mod_cast hsR
    have hsum : δ * (Fintype.card (Fin m) : ℝ) * Fintype.card (Grid k m) ≤
        ∑ b : Grid k m, ((DenseFiber.fiber R b).card : ℝ) := by
      have heq := sum_card_cons_fiber E
      have heqR : (∑ b : Grid k m, ((DenseFiber.fiber R b).card : ℝ)) = E.card := by
        exact_mod_cast heq
      rw [heqR]
      simpa [card_grid, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hdensity
    obtain ⟨A, hA, hcommon⟩ := DenseFiber.exists_common_of_density R s hs δ hδ.le
      (by simpa using hlarge) hsum
    have hδ' : 0 < (δ / 2) ^ s := pow_pos (by positivity) _
    have hδ1' : (δ / 2) ^ s ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have hsteps' : ∀ j < k, 2 * (s : ℝ) ≤ densityIter s ((δ / 2) ^ s) j * m := by
      intro j hj
      rw [← densityIter_shift]
      exact hsteps (j + 1) (Nat.succ_lt_succ hj)
    obtain ⟨B, hBcard, hB⟩ := ih ((δ / 2) ^ s) hδ' hδ1' (DenseFiber.common R A)
      (by simpa using hcommon) hsteps'
    refine ⟨Fin.cons A B, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hA
      · simpa using hBcard j
    · intro i hi
      have htail : Fin.tail i ∈ DenseFiber.common R A := hB _ (fun j => by
        simpa [Fin.tail] using hi j.succ)
      have hhead : i 0 ∈ A := by simpa using hi 0
      have hrel := (DenseFiber.mem_common R A (Fin.tail i)).mp htail (i 0) hhead
      simpa only [R, Fin.cons_self_tail] using hrel

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.DensityConstants` -/


/-!
# The explicit parameters for the dense-box lemma

Starting with density `1/16`, let `a₀ = 4` and `aⱼ₊₁ = s(aⱼ + 1)`.
The estimate `aⱼ + 2 ≤ 6sʲ` suffices to keep all common-fiber steps valid
when `s = D + 1` and `m = 2^(8s^(D-1))`.
-/

namespace VCDimConvexBound

/-- The exponent in the reciprocal-power density lower bound. -/
def densityExponent (s : ℕ) : ℕ → ℕ
  | 0 => 4
  | j + 1 => s * (densityExponent s j + 1)

theorem densityExponent_add_two_le (s : ℕ) (hs : 2 ≤ s) (j : ℕ) :
    densityExponent s j + 2 ≤ 6 * s ^ j := by
  induction j with
  | zero => simp [densityExponent]
  | succ j ih =>
    have h := Nat.mul_le_mul_right s ih
    simp only [densityExponent, pow_succ]
    nlinarith

theorem densityIter_eq_inv_pow (s j : ℕ) :
    densityIter s (1 / 16) j = ((2 : ℝ) ^ densityExponent s j)⁻¹ := by
  induction j with
  | zero => norm_num [densityIter, densityExponent]
  | succ j ih =>
    rw [densityIter, ih]
    have hdiv : ((2 : ℝ) ^ densityExponent s j)⁻¹ / 2 =
        ((2 : ℝ) ^ (densityExponent s j + 1))⁻¹ := by
      rw [pow_succ, mul_inv_rev]
      ring
    rw [hdiv, inv_pow, ← pow_mul]
    simp only [densityExponent, Nat.mul_comm]

theorem densityExponent_budget (s D j : ℕ) (hs : 2 ≤ s) (hD : 2 ≤ D)
    (hj : j < D) : densityExponent s j + 2 * s ≤ 8 * s ^ (D - 1) := by
  have ha := densityExponent_add_two_le s hs j
  have hp : s ^ j ≤ s ^ (D - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsP : s ≤ s ^ (D - 1) := by
    calc
      s = s ^ 1 := (pow_one s).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

/-- All steps have enough room to select `s` distinct coordinates. -/
theorem density_step_budget (D j : ℕ) (hD : 2 ≤ D) (hj : j < D) :
    2 * ((D + 1 : ℕ) : ℝ) ≤ densityIter (D + 1) (1 / 16) j *
      (2 : ℝ) ^ (8 * (D + 1) ^ (D - 1)) := by
  let s := D + 1
  let a := densityExponent s j
  let L := 8 * s ^ (D - 1)
  have ha : a + 2 * s ≤ L := densityExponent_budget s D j (by dsimp [s]; omega) hD hj
  have hnat : (2 * s) * 2 ^ a ≤ 2 ^ L := by
    calc
      (2 * s) * 2 ^ a ≤ 2 ^ (2 * s) * 2 ^ a :=
        Nat.mul_le_mul_right _ (show 2 * s < 2 ^ (2 * s) from Nat.lt_two_pow_self).le
      _ = 2 ^ (a + 2 * s) := by rw [← pow_add, Nat.add_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) ha
  have hreal : (2 * (s : ℝ)) * (2 : ℝ) ^ a ≤ (2 : ℝ) ^ L := by
    exact_mod_cast hnat
  have h := (le_div_iff₀ (show 0 < (2 : ℝ) ^ a by positivity)).mpr hreal
  rw [densityIter_eq_inv_pow]
  simpa only [s, a, L, div_eq_mul_inv, mul_comm] using h

/-- The quantitative complete-box lemma used by the proposed VCₙ proof. -/
theorem containsBox_of_density_one_sixteenth (D : ℕ) (hD : 2 ≤ D)
    (E : Finset (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))))
    (hE : (2 ^ (8 * (D + 1) ^ (D - 1))) ^ D ≤ 16 * E.card) :
    ContainsBox E (D + 1) := by
  apply containsBox_of_density D _ (D + 1) (by positivity) (1 / 16)
    (by norm_num) (by norm_num) E
  · have hreal : (((2 ^ (8 * (D + 1) ^ (D - 1)) : ℕ) : ℝ)) ^ D ≤
        16 * (E.card : ℝ) := by exact_mod_cast hE
    linarith
  · intro j hj
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using density_step_budget D j hD hj

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SparseGenerators` -/


/-!
# The precise remaining geometric input and its sparse-generator consequence

`SanyalBoxObstruction` is a proposition, not an axiom or a proved theorem.
It is the special consequence of Sanyal's Theorem 1.3 required by the VC argument:
the complete sums of D families of D+1 points in R^D cannot be convex independent.
The reference allows lower-dimensional summands (Observation 1).

This file proves the reduction from that explicit input to sparse representatives.
It does not prove the geometric input itself.

Reference: https://arxiv.org/pdf/math/0702717v2
-/

namespace VCDimConvexBound

/-- The geometric input still to be proved, intended for `2 ≤ D`. -/
def SanyalBoxObstruction (D : ℕ) : Prop :=
  ∀ z : Fin D → Fin (D + 1) → Point D,
    ¬ ConvexIndependent ℝ (gridSum z)

/-- A convex-independent family cannot contain a full box if the geometric input holds. -/
theorem not_containsBox_of_sanyal {D m : ℕ}
    (hS : SanyalBoxObstruction D) (z : Fin D → Fin m → Point D)
    (V : Finset (Grid D m)) (hV : ConvexIndependentOn (gridSum z) V) :
    ¬ ContainsBox V (D + 1) := by
  classical
  rintro ⟨A, hA, hAV⟩
  let e (k : Fin D) : Fin (D + 1) ≃ A k :=
    (Fintype.equivFinOfCardEq (by simpa using hA k)).symm
  let emb : Grid D (D + 1) ↪ V :=
    { toFun := fun i => ⟨fun k => (e k (i k)).val,
        hAV _ (fun k => (e k (i k)).property)⟩
      inj' := by
        intro i j h
        funext k
        apply (e k).injective
        apply Subtype.ext
        exact congrFun (congrArg Subtype.val h) k }
  let w : Fin D → Fin (D + 1) → Point D := fun k a => z k (e k a)
  apply hS w
  exact hV.convexIndependent.comp_embedding emb

/-- P3 and the geometric input bound the number of convex-independent representatives. -/
theorem convexIndependent_card_lt_of_sanyal (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D)
    (z : Fin D → Fin (2 ^ (8 * (D + 1) ^ (D - 1))) → Point D)
    (V : Finset (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))))
    (hV : ConvexIndependentOn (gridSum z) V) :
    16 * V.card < (2 ^ (8 * (D + 1) ^ (D - 1))) ^ D := by
  by_contra h
  have hbox := containsBox_of_density_one_sixteenth D hD V (by omega)
  exact not_containsBox_of_sanyal hS z V hV hbox

/-- Every convex label has a sparse hull encoding, conditional on the geometric input. -/
theorem exists_sparse_hull_encoding_of_sanyal (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D)
    (S : Set (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))) )
    (hSlabel : S ∈ convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))) :
    ∃ z : Fin D → Fin (2 ^ (8 * (D + 1) ^ (D - 1))) → Point D,
      ∃ V : Finset (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))),
        ConvexIndependentOn (gridSum z) V ∧
        16 * V.card < (2 ^ (8 * (D + 1) ^ (D - 1))) ^ D ∧
        ∀ i, i ∈ S ↔ gridSum z i ∈ indexedHull (gridSum z) V := by
  obtain ⟨C, hC, z, hz⟩ := mem_convexLabels.mp hSlabel
  obtain ⟨V, _, hV, _, hlabels⟩ := exists_label_generators (gridSum z) C hC
  exact ⟨z, V, hV, convexIndependent_card_lt_of_sanyal D hD hS z V hV,
    fun i => (hz i).symm.trans (hlabels i)⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SanyalSeparation` -/


/-!
# Strict supporting functionals for the Sanyal obstruction

For a finite configuration, convex independence is equivalent to a strict
linear supporting functional at each indexed point. For additive arrays,
the same functional must select the chosen point in every summand.
These are proved reductions, not a proof of the remaining obstruction.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Finite convex independence is witnessed by strict supporting functionals. -/
theorem convexIndependent_iff_strict_support {ι : Type*} [Fintype ι] {D : ℕ}
    (q : ι → Point D) :
    ConvexIndependent ℝ q ↔
      ∀ i, ∃ f : Point D →L[ℝ] ℝ, ∀ j, j ≠ i → f (q j) < f (q i) := by
  constructor
  · intro h i
    have hout : q i ∉ convexHull ℝ (q '' {j | j ≠ i}) := by
      intro hi
      exact h _ i hi rfl
    obtain ⟨f, u, hf, hui⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) ((Set.toFinite _).isClosed_convexHull ℝ) hout
    exact ⟨f, fun j hji => (hf _ (subset_convexHull ℝ _ ⟨j, hji, rfl⟩)).trans hui⟩
  · intro h s i hi
    by_contra his
    obtain ⟨f, hf⟩ := h i
    have hs : convexHull ℝ (q '' s) ⊆ {x | f x < f (q i)} := by
      apply convexHull_min _ (convex_halfSpace_lt ⟨f.map_add, f.map_smul⟩ _)
      rintro _ ⟨j, hj, rfl⟩
      exact hf j (fun hji => his (hji ▸ hj))
    exact (lt_irrefl (f (q i))) (hs hi)

/-- Convex independence of a finite configuration persists under small perturbations. -/
theorem isOpen_convexIndependent {ι : Type*} [Fintype ι] {D : ℕ} :
    IsOpen {q : ι → Point D | ConvexIndependent ℝ q} := by
  simp only [convexIndependent_iff_strict_support, Set.ofPred_forall, Set.ofPred_exists]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iUnion
  intro f
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt (f.continuous.comp (continuous_apply j))
    (f.continuous.comp (continuous_apply i))

/-- One linear functional strictly selects the prescribed point in every family. -/
def CommonStrictMaximizers {r m D : ℕ} (z : Fin r → Fin m → Point D) : Prop :=
  ∀ i : Grid r m, ∃ f : Point D →L[ℝ] ℝ,
    ∀ k j, j ≠ i k → f (z k j) < f (z k (i k))

/-- Changing one summand in an additive array. -/
theorem gridSum_update {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (i : Grid r m) (k : Fin r) (j : Fin m) :
    gridSum z (Function.update i k j) = gridSum z i - z k (i k) + z k j := by
  classical
  have he : (fun a => z a (Function.update i k j a)) =
      Function.update (fun a => z a (i a)) k (z k j) := by
    funext a
    by_cases ha : a = k <;> simp [ha]
  simp only [gridSum, he, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hs := Finset.sum_erase_add Finset.univ (fun a => z a (i a)) (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← hs]
  abel

/-- All sums are vertices exactly when every choice admits a common strict support. -/
theorem convexIndependent_gridSum_iff_commonStrictMaximizers {r m D : ℕ}
    (z : Fin r → Fin m → Point D) :
    ConvexIndependent ℝ (gridSum z) ↔ CommonStrictMaximizers z := by
  rw [convexIndependent_iff_strict_support]
  constructor
  · intro h i
    obtain ⟨f, hf⟩ := h i
    refine ⟨f, fun k j hji => ?_⟩
    have hne : Function.update i k j ≠ i := by
      intro he
      exact hji (by simpa using congrFun he k)
    have hlt := hf (Function.update i k j) hne
    rw [gridSum_update, map_add, map_sub] at hlt
    linarith
  · intro h i
    obtain ⟨f, hf⟩ := h i
    refine ⟨f, fun j hji => ?_⟩
    have hex : ∃ k, j k ≠ i k := Function.ne_iff.mp hji
    simp only [gridSum, map_sum]
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : j k = i k
      · simp [hk]
      · exact (hf k (j k) hk).le
    · obtain ⟨k, hk⟩ := hex
      exact ⟨k, Finset.mem_univ k, hf k (j k) hk⟩

/-- The set of counterexample arrays is open, including at degenerate configurations. -/
theorem isOpen_convexIndependent_gridSum (r m D : ℕ) :
    IsOpen {z : Fin r → Fin m → Point D | ConvexIndependent ℝ (gridSum z)} := by
  apply isOpen_convexIndependent.preimage
  unfold gridSum
  fun_prop

/-- The original geometric input is equivalent to failure of some common strict support. -/
theorem sanyalBoxObstruction_iff_no_commonStrictMaximizers (D : ℕ) :
    SanyalBoxObstruction D ↔
      ∀ z : Fin D → Fin (D + 1) → Point D, ¬ CommonStrictMaximizers z := by
  simp only [SanyalBoxObstruction, convexIndependent_gridSum_iff_commonStrictMaximizers]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SimplexPerturbation` -/


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


/-! ## Source module `VCDimConvexBound.SanyalCertificates` -/


/-!
# A finite linear certificate for a lost vertex of the Minkowski sum

At a chosen corner, take all edges obtained by changing exactly one summand.
The sum fails to have a strict supporting functional exactly when these edge
vectors admit nonnegative weights summing to one and with weighted sum zero.
The unresolved Sanyal core is reduced to producing such a corner for simplices.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Finite strict separation from zero, including the empty family. -/
theorem zero_mem_convexHull_iff_no_strict_separator {ι : Type*} [Fintype ι] {D : ℕ}
    (q : ι → Point D) :
    (0 : Point D) ∈ convexHull ℝ (Set.range q) ↔
      ¬ ∃ f : Point D →L[ℝ] ℝ, ∀ j, f (q j) < 0 := by
  constructor
  · rintro hzero ⟨f, hf⟩
    have hs : convexHull ℝ (Set.range q) ⊆ {x | f x < 0} := by
      apply convexHull_min _ (convex_halfSpace_lt ⟨f.map_add, f.map_smul⟩ _)
      rintro _ ⟨j, rfl⟩
      exact hf j
    have h : f 0 < 0 := hs hzero
    simp at h
  · intro h
    by_contra hzero
    obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) ((Set.finite_range q).isClosed_convexHull ℝ) hzero
    apply h
    exact ⟨f, fun j => by simpa using (hf _ (subset_convexHull ℝ _ ⟨j, rfl⟩)).trans hu⟩

/-- Edges incident to one vertex of the product of the indexed point sets. -/
abbrev CornerEdge {r m : ℕ} (i : Grid r m) :=
  {e : Fin r × Fin m // e.2 ≠ i e.1}

/-- The image of an incident edge under the summation projection. -/
def cornerVector {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (i : Grid r m) (e : CornerEdge i) : Point D :=
  z e.val.1 e.val.2 - z e.val.1 (i e.val.1)

/-- A normalized nonnegative dependence among the projected incident edges. -/
def BalancedCorner {r m D : ℕ} (z : Fin r → Fin m → Point D) (i : Grid r m) : Prop :=
  ∃ w : CornerEdge i → ℝ, (∀ e, 0 ≤ w e) ∧
    ∑ e, w e = 1 ∧ ∑ e, w e • cornerVector z i e = 0

/-- The coefficient certificate exactly detects failure of a common support at this corner. -/
theorem balancedCorner_iff_no_support {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) :
    BalancedCorner z i ↔ ¬ ∃ f : Point D →L[ℝ] ℝ,
      ∀ k j, j ≠ i k → f (z k j) < f (z k (i k)) := by
  rw [BalancedCorner, ← mem_convexHull_range_iff_weights, zero_mem_convexHull_iff_no_strict_separator]
  apply not_congr
  apply exists_congr
  intro f
  constructor
  · intro h k j hji
    have he := h ⟨(k, j), hji⟩
    simpa only [cornerVector, map_sub, sub_lt_zero] using he
  · intro h e
    simpa only [cornerVector, map_sub, sub_lt_zero] using h e.val.1 e.val.2 e.property

/-- A non-independent array always has a corner carrying a finite balance certificate. -/
theorem not_convexIndependent_gridSum_iff_balancedCorner {r m D : ℕ}
    (z : Fin r → Fin m → Point D) :
    ¬ ConvexIndependent ℝ (gridSum z) ↔ ∃ i, BalancedCorner z i := by
  classical
  simp only [convexIndependent_gridSum_iff_commonStrictMaximizers,
    CommonStrictMaximizers, not_forall, balancedCorner_iff_no_support]

/-- Exact remaining Sanyal obligation after eliminating degeneracies and separation. -/
theorem sanyalBoxObstruction_iff_simplex_balancing (D : ℕ) :
    SanyalBoxObstruction D ↔
      ∀ z : Fin D → Fin (D + 1) → Point D,
        (∀ k, AffineIndependent ℝ (z k)) → ∃ i, BalancedCorner z i := by
  simp only [sanyalBoxObstruction_iff_simplex_obstruction,
    not_convexIndependent_gridSum_iff_balancedCorner]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SanyalGale` -/


/-!
# The kernel configuration used by Sanyal's projection argument

Use barycentric coordinates on the product of point families. The kernel consists
of coefficient arrays with zero sum in each row and zero weighted image. Restrict
coordinate evaluations to this kernel. At any strictly supported corner, the
remaining evaluations positively span its dual. No non-embedding theorem is
assumed or proved here.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Every vector is a nonnegative combination of the indexed vectors. -/
def PositivelySpans {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (q : ι → E) : Prop :=
  ∀ y, ∃ a : ι → ℝ, (∀ j, 0 ≤ a j) ∧ ∑ j, a j • q j = y

/-- A strictly positive dependence lets one shift arbitrary coefficients to nonnegative ones. -/
theorem positivelySpans_of_span_eq_top_of_positive_dependence
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (q : ι → E) (hs : Submodule.span ℝ (Set.range q) = ⊤)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) (hz : ∑ j, w j • q j = 0) :
    PositivelySpans q := by
  classical
  intro y
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (show y ∈ Submodule.span ℝ (Set.range q) by rw [hs]; trivial)
  let t : ℝ := ∑ j, |a j| / w j
  refine ⟨fun j => a j + t * w j, fun j => ?_, ?_⟩
  · have hle : -a j / w j ≤ t := by
      apply (div_le_div_of_nonneg_right (neg_le_abs (a j)) (hw j).le).trans
      exact Finset.single_le_sum (fun k _ => div_nonneg (abs_nonneg _) (hw k).le)
        (Finset.mem_univ j)
    have := (div_le_iff₀ (hw j)).mp hle
    linarith
  · simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, hz, smul_zero, add_zero]
    exact ha

/-- Positive spanning persists when more generators are available. -/
theorem PositivelySpans.subtype_mono {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (v : ι → E)
    {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ j, p j → q j)
    (h : PositivelySpans (fun j : {j // p j} => v j.val)) :
    PositivelySpans (fun j : {j // q j} => v j.val) := by
  classical
  intro y
  obtain ⟨w, hw, hwy⟩ := h y
  let a : ι → ℝ := fun j => if hj : p j then w ⟨j, hj⟩ else 0
  refine ⟨fun j => a j.val, fun j => ?_, ?_⟩
  · dsimp [a]
    split_ifs with hj
    · exact hw ⟨j.val, hj⟩
    · exact le_rfl
  · have hp : (∑ j, a j • v j) = ∑ j : {j // p j}, w j • v j.val := by
      simpa only using! (Finset.sum_congr_set (Set.ofPred p)
        (fun j => a j • v j) (fun j => w j • v j.val)
        (by intro j hj; change p j at hj; simp [a, hj])
        (by intro j hj; change ¬ p j at hj; simp [a, hj]))
    have hq : (∑ j, a j • v j) = ∑ j : {j // q j}, a j.val • v j.val := by
      simpa only using! (Finset.sum_congr_set (Set.ofPred q)
        (fun j => a j • v j) (fun j => a j.val • v j.val)
        (by intros; rfl) (by
          intro j hj
          have hnp : ¬ p j := fun h => hj (hpq j h)
          simp [a, hnp]))
    rw [← hq, hp, hwy]

/-- The deletion property in the definition of a Gale configuration. -/
def IsGaleConfiguration {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] (v : ι → E) : Prop :=
  ∀ j, PositivelySpans (fun k : {k : ι // k ≠ j} => v k.val)

/-- Infinitesimal barycentric motions invisible under the summation projection. -/
def cayleyKernel {r m D : ℕ} (z : Fin r → Fin m → Point D) :
    Submodule ℝ ((Fin r × Fin m) → ℝ) where
  carrier := {x | (∀ k, ∑ j, x (k, j) = 0) ∧ ∑ e, x e • z e.1 e.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hxz⟩ ⟨hy, hyz⟩
    constructor
    · intro k
      simpa only [Pi.add_apply, Finset.sum_add_distrib, hx, hy] using (add_zero (0 : ℝ))
    · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hxz, hyz, add_zero]
  smul_mem' := by
    rintro a x ⟨hx, hxz⟩
    constructor
    · intro k
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hxz, smul_zero]

/-- Coordinate evaluations restricted to the projection kernel. -/
def galeVector {r m D : ℕ} (z : Fin r → Fin m → Point D) (e : Fin r × Fin m) :
    Module.Dual ℝ (cayleyKernel z) :=
  (LinearMap.proj e).comp (cayleyKernel z).subtype

@[simp] theorem galeVector_apply {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (e : Fin r × Fin m) (x : cayleyKernel z) : galeVector z e x = x.val e := rfl

/-- Off-corner coordinates determine a kernel vector; the omitted coordinate is its row sum. -/
theorem cayleyKernel_eq_zero_of_corner_coordinates {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (x : cayleyKernel z)
    (hx : ∀ e : CornerEdge i, x.val e.val = 0) : x = 0 := by
  classical
  apply Subtype.ext
  funext e
  change x.val e = 0
  rcases e with ⟨k, j⟩
  by_cases h : j = i k
  · have hs : ∑ j, x.val (k, j) = x.val (k, i k) := by
      apply Finset.sum_eq_single (i k)
      · intro j _ hj
        exact hx ⟨(k, j), hj⟩
      · simp
    have hh := x.property.1 k
    rw [hs] at hh
    simpa only [h] using hh
  · exact hx ⟨(k, j), h⟩

/-- For every corner, its incident facet evaluations span the entire kernel dual. -/
theorem span_corner_galeVectors {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) :
    Submodule.span ℝ (Set.range (fun e : CornerEdge i => galeVector z e.val)) = ⊤ := by
  apply top_unique
  intro f _
  apply mem_span_of_iInf_ker_le_ker
  intro x hx
  have hz : x = 0 := cayleyKernel_eq_zero_of_corner_coordinates z i x fun e => by
    exact ((Submodule.mem_iInf _).mp hx e)
  simp [hz]

/-- A function vanishing on the selected coordinates can be summed over the incident facets. -/
theorem sum_corner_eq_sum_of_zero {r m : ℕ} {E : Type*} [AddCommMonoid E]
    (i : Grid r m) (f : (Fin r × Fin m) → E) (hf : ∀ k, f (k, i k) = 0) :
    ∑ e : CornerEdge i, f e.val = ∑ e, f e := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun e : Fin r × Fin m => e.2 ≠ i e.1)
    (by simp) f]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e _ he
  have h : e.2 = i e.1 := by simpa using he
  rcases e with ⟨k, j⟩
  change j = i k at h
  subst j
  exact hf k

/-- Support gaps give a strictly positive dependence among the incident facet evaluations. -/
theorem positive_dependence_corner_galeVectors {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m)
    (f : Point D →L[ℝ] ℝ)
    (hf : ∀ k j, j ≠ i k → f (z k j) < f (z k (i k))) :
    ∃ w : CornerEdge i → ℝ, (∀ e, 0 < w e) ∧
      ∑ e, w e • galeVector z e.val = 0 := by
  classical
  refine ⟨fun e => f (z e.val.1 (i e.val.1)) - f (z e.val.1 e.val.2),
    fun e => sub_pos.mpr (hf _ _ e.property), ?_⟩
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, galeVector_apply,
    LinearMap.zero_apply, smul_eq_mul]
  rw [sum_corner_eq_sum_of_zero i
    (fun e => (f (z e.1 (i e.1)) - f (z e.1 e.2)) * x.val e)
    (by intro k; simp)]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hrow : (∑ e : Fin r × Fin m, f (z e.1 (i e.1)) * x.val e) = 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, x.property.1, mul_zero]
    simp
  have himage : (∑ e : Fin r × Fin m, f (z e.1 e.2) * x.val e) = 0 := by
    have h := congrArg f x.property.2
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero, mul_comm] using h
  rw [hrow, himage, sub_self]

/-- The projection lemma needed here: strict support forces positive spanning in the kernel dual. -/
theorem positivelySpans_corner_galeVectors_of_support {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m)
    (h : ∃ f : Point D →L[ℝ] ℝ,
      ∀ k j, j ≠ i k → f (z k j) < f (z k (i k))) :
    PositivelySpans (fun e : CornerEdge i => galeVector z e.val) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨w, hw, hz⟩ := positive_dependence_corner_galeVectors z i f hf
  exact positivelySpans_of_span_eq_top_of_positive_dependence _
    (span_corner_galeVectors z i) w hw hz

/-- A hypothetical counterexample gives positive spanning at every corner. -/
theorem positivelySpans_corner_galeVectors_of_convexIndependent {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i : Grid r m) :
    PositivelySpans (fun e : CornerEdge i => galeVector z e.val) :=
  positivelySpans_corner_galeVectors_of_support z i
    ((convexIndependent_gridSum_iff_commonStrictMaximizers z).mp hz i)

/-- Deleting any one vector still leaves a positively spanning configuration. -/
theorem isGaleConfiguration_of_convexIndependent_gridSum {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    IsGaleConfiguration (galeVector z) := by
  intro a
  let i : Grid r m := fun _ => a.2
  apply PositivelySpans.subtype_mono (galeVector z)
    (p := fun e => e.2 ≠ i e.1)
  · intro e he hea
    subst e
    exact he rfl
  · exact positivelySpans_corner_galeVectors_of_convexIndependent z hz i

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.CayleyDimension` -/


/-!
# Dimension of the projection-kernel configuration

Record row sums together with the weighted image. If one point family is a
full-dimensional simplex, this linear map is onto. Rank-nullity then gives
r(D+1) - (r+D) dimensions for the kernel, or D²-D for r=D.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The linear map recording row masses and the weighted point sum. -/
def cayleyMap {r m D : ℕ} (z : Fin r → Fin m → Point D) :
    ((Fin r × Fin m) → ℝ) →ₗ[ℝ] ((Fin r → ℝ) × Point D) where
  toFun x := (fun k => ∑ j, x (k, j), ∑ e, x e • z e.1 e.2)
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib, add_smul]
  map_smul' a x := by
    ext <;> simp [Finset.mul_sum, mul_smul]

/-- The barycentric kernel is the ordinary kernel of the Cayley linear map. -/
theorem ker_cayleyMap {r m D : ℕ} (z : Fin r → Fin m → Point D) :
    LinearMap.ker (cayleyMap z) = cayleyKernel z := by
  ext x
  simp [LinearMap.mem_ker, cayleyMap, cayleyKernel, Prod.ext_iff, funext_iff]

@[simp] theorem cayleyMap_single {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (e : Fin r × Fin m) :
    cayleyMap z (Pi.single e 1) = (Pi.single e.1 1, z e.1 e.2) := by
  classical
  apply Prod.ext
  · funext k
    change (∑ j, (Pi.single e 1 : (Fin r × Fin m) → ℝ) (k, j)) =
      (Pi.single e.1 1 : Fin r → ℝ) k
    by_cases h : k = e.1
    · subst k
      simp [Pi.single_apply, Prod.ext_iff]
    · simp [Prod.ext_iff, h]
  · change (∑ a, (Pi.single e 1 : (Fin r × Fin m) → ℝ) a • z a.1 a.2) = z e.1 e.2
    simp [Pi.single_apply]

/-- Edge vectors from the base vertex of a full-dimensional simplex span the ambient space. -/
theorem span_simplex_edges_eq_top {D : ℕ} (q : Fin (D + 1) → Point D)
    (hq : AffineIndependent ℝ q) :
    Submodule.span ℝ (Set.range (fun j : Fin D => q j.succ - q 0)) = ⊤ := by
  have hl := (affineIndependent_iff_linearIndependent_vsub ℝ q 0).mp hq
  have he : LinearIndependent ℝ (fun j : Fin D => q j.succ - q 0) := by
    simpa [Function.comp_def, finSuccAboveEquiv_apply] using!
      (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (D + 1)))).mpr hl
  exact he.span_eq_top_of_card_eq_finrank' (by simp [Point])

/-- One simplex family suffices to make the Cayley map surjective. -/
theorem range_cayleyMap_eq_top_of_simplex {r D : ℕ}
    (z : Fin r → Fin (D + 1) → Point D) (k : Fin r)
    (hk : AffineIndependent ℝ (z k)) :
    LinearMap.range (cayleyMap z) = ⊤ := by
  classical
  let K := LinearMap.range (cayleyMap z)
  have hedge (j : Fin D) : (0, z k j.succ - z k 0) ∈ K := by
    refine ⟨Pi.single (k, j.succ) 1 - Pi.single (k, 0) 1, ?_⟩
    rw [map_sub, cayleyMap_single, cayleyMap_single]
    simp
  have hspan : Submodule.span ℝ (Set.range (fun j : Fin D => z k j.succ - z k 0)) ≤
      K.comap (LinearMap.inr ℝ (Fin r → ℝ) (Point D)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hedge j
  rw [span_simplex_edges_eq_top (z k) hk] at hspan
  have hzero (y : Point D) : (0, y) ∈ K := hspan (Submodule.mem_top)
  apply top_unique
  rintro ⟨a, y⟩ _
  have hbase : (a, ∑ l, a l • z l 0) ∈ K := by
    refine ⟨fun e => if e.2 = 0 then a e.1 else 0, ?_⟩
    apply Prod.ext
    · funext l
      simp [cayleyMap]
    · change (∑ e : Fin r × Fin (D + 1),
        (if e.2 = 0 then a e.1 else 0) • z e.1 e.2) = _
      rw [Fintype.sum_prod_type]
      simp
  have h := K.add_mem hbase (hzero (y - ∑ l, a l • z l 0))
  simpa [K] using h

/-- Exact rank-nullity, without truncated-subtraction side conditions. -/
theorem finrank_cayleyKernel_add {r D : ℕ}
    (z : Fin r → Fin (D + 1) → Point D) (k : Fin r)
    (hk : AffineIndependent ℝ (z k)) :
    Module.finrank ℝ (cayleyKernel z) + (r + D) = r * (D + 1) := by
  have h := (cayleyMap z).finrank_range_add_finrank_ker
  rw [ker_cayleyMap, range_cayleyMap_eq_top_of_simplex z k hk] at h
  simpa [Module.finrank_prod, Point, Nat.add_comm] using h

/-- The kernel-dual configuration for D simplices lives in dimension D²-D. -/
theorem finrank_galeSpace {D : ℕ} (hD : 0 < D)
    (z : Fin D → Fin (D + 1) → Point D)
    (hz : ∀ k, AffineIndependent ℝ (z k)) :
    Module.finrank ℝ (Module.Dual ℝ (cayleyKernel z)) = D * (D - 1) := by
  rw [Subspace.dual_finrank_eq]
  have h := finrank_cayleyKernel_add z ⟨0, hD⟩ (hz ⟨0, hD⟩)
  have hd : D - 1 + 1 = D := Nat.sub_add_cancel hD
  nlinarith

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.CayleyFaces` -/


/-!
# A direct Cayley realization of the colorful faces

For the standard product needed by the VC argument, append the color basis
vector to each input point. Common strict support then exposes every subset
of a transversal. These simplices meet exactly along their common vertices,
so they form a geometric simplicial complex in mathlib. No general Gale
polytope duality or non-embedding theorem is used.
-/

namespace VCDimConvexBound

open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev CayleySpace (r D : ℕ) := (Fin r → ℝ) × Point D

/-- A point together with its color coordinate. -/
def cayleyPoint {r m D : ℕ} (z : Fin r → Fin m → Point D) (e : Fin r × Fin m) :
    CayleySpace r D := (Pi.single e.1 1, z e.1 e.2)

/-- Transversals are independent already in the color coordinates. -/
theorem linearIndependent_cayleyCorner {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) :
    LinearIndependent ℝ (fun k => cayleyPoint z (k, i k)) := by
  apply LinearIndependent.of_comp (LinearMap.fst ℝ (Fin r → ℝ) (Point D))
  exact Pi.linearIndependent_single_one (Fin r) ℝ

theorem affineIndependent_cayleyCorner {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) :
    AffineIndependent ℝ (fun k => cayleyPoint z (k, i k)) :=
  (linearIndependent_cayleyCorner z i).affineIndependent

/-- Penalize the omitted colors as well as the unselected points. -/
noncomputable def cayleySupport {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (i : Grid r m) (S : Set (CayleySpace r D)) (f : Point D →L[ℝ] ℝ) :
    CayleySpace r D →L[ℝ] ℝ := by
  classical
  let c : Fin r → ℝ := fun k => f (z k (i k)) +
    if cayleyPoint z (k, i k) ∈ S then 0 else 1
  exact LinearMap.toContinuousLinearMap {
    toFun := fun x => f x.2 - ∑ k, x.1 k * c k
    map_add' := by
      intro x y
      simp only [Prod.snd_add, map_add, Prod.fst_add, Pi.add_apply,
        add_mul, Finset.sum_add_distrib]
      ring
    map_smul' := by
      intro a x
      change f (a • x.2) - ∑ k, (a * x.1 k) * c k =
        a * (f x.2 - ∑ k, x.1 k * c k)
      simp only [map_smul, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_sub] }

@[simp] theorem cayleySupport_apply_point {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (S : Set (CayleySpace r D))
    (f : Point D →L[ℝ] ℝ) (e : Fin r × Fin m) :
    cayleySupport z i S f (cayleyPoint z e) = f (z e.1 e.2) -
      (f (z e.1 (i e.1)) + if cayleyPoint z (e.1, i e.1) ∈ S then 0 else 1) := by
  classical
  simp [cayleySupport, cayleyPoint, Pi.single_apply]

/-- The exposing functional is nonpositive on every Cayley generator. -/
theorem cayleySupport_nonpos {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (S : Set (CayleySpace r D))
    (f : Point D →L[ℝ] ℝ)
    (hf : ∀ k j, j ≠ i k → f (z k j) < f (z k (i k))) (e : Fin r × Fin m) :
    cayleySupport z i S f (cayleyPoint z e) ≤ 0 := by
  classical
  have hle : f (z e.1 e.2) ≤ f (z e.1 (i e.1)) := by
    by_cases h : e.2 = i e.1
    · rw [h]
    · exact (hf _ _ h).le
  rw [cayleySupport_apply_point]
  split_ifs <;> linarith

/-- Exactly the prescribed transversal subset lies on the supporting hyperplane. -/
theorem cayleySupport_eq_zero_iff {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k)))
    (f : Point D →L[ℝ] ℝ)
    (hf : ∀ k j, j ≠ i k → f (z k j) < f (z k (i k))) (e : Fin r × Fin m) :
    cayleySupport z i S f (cayleyPoint z e) = 0 ↔ cayleyPoint z e ∈ S := by
  classical
  rcases e with ⟨k, j⟩
  constructor
  · intro hzero
    have hj : j = i k := by
      by_contra hj
      have hlt := hf k j hj
      rw [cayleySupport_apply_point] at hzero
      split_ifs at hzero <;> linarith
    subst j
    by_contra hs
    simp [hs] at hzero
  · intro hs
    obtain ⟨l, hl⟩ := hS hs
    rw [← hl] at hs ⊢
    simp [hs]

/-- Every subset of a transversal admits an exact global exposing functional. -/
theorem exists_cayley_face_support {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k))) :
    ∃ g : CayleySpace r D →L[ℝ] ℝ,
      (∀ x ∈ Set.range (cayleyPoint z), g x ≤ 0) ∧
      (∀ x ∈ Set.range (cayleyPoint z), g x = 0 ↔ x ∈ S) := by
  obtain ⟨f, hf⟩ := (convexIndependent_gridSum_iff_commonStrictMaximizers z).mp hz i
  refine ⟨cayleySupport z i S f, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩
    exact cayleySupport_nonpos z i S f hf e
  · rintro _ ⟨e, rfl⟩
    exact cayleySupport_eq_zero_iff z i S hS f hf e

/-- A transversal subset uses only generators of the Cayley polytope. -/
theorem subset_cayley_range_of_subset_corner {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k))) :
    S ⊆ Set.range (cayleyPoint z) := by
  intro x hx
  obtain ⟨k, rfl⟩ := hS hx
  exact Set.mem_range_self (k, i k)

/-- The colorful simplices are genuine exposed faces of the finite Cayley hull. -/
theorem isExposed_cayley_face {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k))) :
    IsExposed ℝ (convexHull ℝ (Set.range (cayleyPoint z))) (convexHull ℝ S) := by
  obtain ⟨f, hf, hfS⟩ := exists_cayley_face_support z hz i S hS
  exact isExposed_convexHull_of_zero_face _ S (Set.finite_range _)
    (subset_cayley_range_of_subset_corner z i S hS) f hf hfS

/-- Colorful faces intersect in precisely the convex hull of their common vertices. -/
theorem cayley_faces_inter {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i j : Grid r m) (S T : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k)))
    (hT : T ⊆ Set.range (fun k => cayleyPoint z (k, j k))) :
    convexHull ℝ S ∩ convexHull ℝ T = convexHull ℝ (S ∩ T) := by
  obtain ⟨f, hf, hfS⟩ := exists_cayley_face_support z hz i S hS
  exact convexHull_inter_convexHull_of_zero_face _ S T (Set.finite_range _)
    (subset_cayley_range_of_subset_corner z i S hS)
    (subset_cayley_range_of_subset_corner z j T hT) f.toLinearMap hf hfS

/-- The family of nonempty colorful simplices, with the geometric gluing proof included. -/
noncomputable def cayleyComplex {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    Geometry.SimplicialComplex ℝ (CayleySpace r D) := by
  classical
  apply Geometry.SimplicialComplex.ofErase
    {s | ∃ i : Grid r m, (s : Set (CayleySpace r D)) ⊆
      Set.range (fun k => cayleyPoint z (k, i k))}
  · rintro s ⟨i, hs⟩
    exact (affineIndependent_cayleyCorner z i).range.mono hs
  · intro s t hts hs
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, fun x hx => hi (hts hx)⟩
  · rintro s ⟨i, hs⟩ t ⟨j, ht⟩
    exact (cayley_faces_inter z hz i j _ _ hs ht).le

/-- The constructed complex has exactly the nonempty subsets of transversals as faces. -/
theorem mem_cayleyComplex_faces {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (s : Finset (CayleySpace r D)) :
    s ∈ (cayleyComplex z hz).faces ↔ s.Nonempty ∧
      ∃ i : Grid r m, (s : Set (CayleySpace r D)) ⊆
        Set.range (fun k => cayleyPoint z (k, i k)) := by
  classical
  change ((∃ i : Grid r m, (s : Set (CayleySpace r D)) ⊆
    Set.range (fun k => cayleyPoint z (k, i k))) ∧ s ∉ ({∅} : Set _)) ↔ _
  simp only [Set.mem_singleton_iff, Finset.nonempty_iff_ne_empty, and_comm]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.ColorfulComplex` -/


/-!
# Identification of the colorful complex

Its abstract faces contain at most one point of each color. The Cayley map is
injective under the hypothetical counterexample, and its images are exactly
the faces of the constructed geometric simplicial complex.
-/

namespace VCDimConvexBound

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The join of r discrete m-point sets, described by its nonempty faces. -/
def colorfulComplex (r m : ℕ) : AbstractSimplicialComplex (Fin r × Fin m) where
  faces := {s | s.Nonempty ∧ Set.InjOn Prod.fst (s : Set (Fin r × Fin m))}
  isRelLowerSet_faces := by
    rintro s ⟨hn, hi⟩
    refine ⟨hn, ?_⟩
    intro t hts ht
    exact ⟨ht, hi.mono hts⟩
  singleton_mem := by
    intro e
    refine ⟨Finset.singleton_nonempty e, ?_⟩
    simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst e

/-- A nonempty colorful set extends to a full transversal, including empty color classes. -/
theorem colorful_iff_subset_transversal {r m : ℕ}
    (s : Finset (Fin r × Fin m)) (hs : s.Nonempty) :
    Set.InjOn Prod.fst (s : Set (Fin r × Fin m)) ↔
      ∃ i : Grid r m, ∀ e ∈ s, e.2 = i e.1 := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha⟩ := hs
    let i : Grid r m := fun k => if h : ∃ j, (k, j) ∈ s then h.choose else a.2
    refine ⟨i, fun e he => ?_⟩
    have hex : ∃ j, (e.1, j) ∈ s := ⟨e.2, he⟩
    have hei : (e.1, i e.1) ∈ s := by
      simpa only [i, dite_eq_left hex] using hex.choose_spec
    exact congrArg Prod.snd (hi he hei rfl)
  · rintro ⟨i, hi⟩ a ha b hb hab
    exact Prod.ext hab (by rw [hi a ha, hi b hb, hab])

/-- Distinct colors have distinct Cayley coordinates. -/
theorem cayleyPoint_color_eq_of_eq {r m D : ℕ}
    (z : Fin r → Fin m → Point D) {a b : Fin r × Fin m}
    (h : cayleyPoint z a = cayleyPoint z b) : a.1 = b.1 := by
  classical
  by_contra hn
  have h' := congrArg (fun x : CayleySpace r D => x.1 a.1) h
  simp [cayleyPoint, hn] at h'

/-- Under a hypothetical counterexample, no vertices are identified by the Cayley realization. -/
theorem cayleyPoint_injective_of_convexIndependent {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    Function.Injective (cayleyPoint z) := by
  intro a b hab
  have hk := cayleyPoint_color_eq_of_eq z hab
  apply Prod.ext hk
  by_contra hj
  let i : Grid r m := fun _ => a.2
  obtain ⟨f, hf⟩ := (convexIndependent_gridSum_iff_commonStrictMaximizers z).mp hz i
  have hlt := hf b.1 b.2 (Ne.symm hj)
  have heq : z a.1 a.2 = z b.1 b.2 := congrArg Prod.snd hab
  dsimp [i] at hlt
  rw [hk] at heq
  rw [← heq] at hlt
  exact lt_irrefl _ hlt

/-- Exactly the abstract colorful faces occur as geometric Cayley faces. -/
theorem mem_cayleyComplex_image_iff {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (s : Finset (Fin r × Fin m)) :
    s.image (cayleyPoint z) ∈ (cayleyComplex z hz).faces ↔
      s ∈ (colorfulComplex r m).faces := by
  classical
  rw [mem_cayleyComplex_faces]
  change (s.image (cayleyPoint z)).Nonempty ∧ _ ↔ s.Nonempty ∧ _
  rw [Finset.image_nonempty]
  apply and_congr_right
  intro hs
  rw [colorful_iff_subset_transversal s hs]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun e he => ?_⟩
    obtain ⟨k, hk⟩ := hi (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    have h := cayleyPoint_injective_of_convexIndependent z hz hk
    rw [← h]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨e.1, ?_⟩
    have h : (e.1, i e.1) = e := Prod.ext rfl (hi e he).symm
    exact congrArg (cayleyPoint z) h

/-- Equality of the abstract face structures, not just a map on individual vertices. -/
theorem cayleyComplex_eq_map_colorful {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    (cayleyComplex z hz).toPreAbstractSimplicialComplex =
      (colorfulComplex r m).toPreAbstractSimplicialComplex.map (cayleyPoint z) := by
  classical
  apply PreAbstractSimplicialComplex.ext
  ext s
  change s ∈ (cayleyComplex z hz).faces ↔
    ∃ t ∈ (colorfulComplex r m).faces, t.image (cayleyPoint z) = s
  constructor
  · intro hs
    obtain ⟨_, i, hi⟩ := (mem_cayleyComplex_faces z hz s).mp hs
    let t : Finset (Fin r × Fin m) := Finset.univ.filter fun e => cayleyPoint z e ∈ s
    have hts : t.image (cayleyPoint z) = s := by
      ext x
      constructor
      · intro hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp he).2
      · intro hx
        obtain ⟨k, hk⟩ := hi hx
        exact Finset.mem_image.mpr ⟨(k, i k), by simp [t, hk, hx], hk⟩
    refine ⟨t, (mem_cayleyComplex_image_iff z hz t).mp ?_, hts⟩
    rwa [hts]
  · rintro ⟨t, ht, rfl⟩
    exact (mem_cayleyComplex_image_iff z hz t).mpr ht

/-- Every Cayley generator is an exposed vertex of the finite hull. -/
theorem cayleyPoint_mem_exposedPoints {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (e : Fin r × Fin m) :
    cayleyPoint z e ∈ (convexHull ℝ (Set.range (cayleyPoint z))).exposedPoints ℝ := by
  rw [mem_exposedPoints_iff_exposed_singleton]
  have h := isExposed_cayley_face z hz (fun _ => e.2) {cayleyPoint z e} (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨e.1, rfl⟩)
  simpa only [convexHull_singleton] using h

/-- The constructed complex has all and only the indexed Cayley points as vertices. -/
theorem cayleyComplex_vertices {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    (cayleyComplex z hz).vertices = Set.range (cayleyPoint z) := by
  classical
  ext x
  rw [Geometry.SimplicialComplex.mem_vertices, mem_cayleyComplex_faces]
  constructor
  · rintro ⟨_, i, hi⟩
    exact subset_cayley_range_of_subset_corner z i _ hi (Finset.mem_singleton_self x)
  · rintro ⟨e, rfl⟩
    refine ⟨Finset.singleton_nonempty _, (fun _ => e.2), ?_⟩
    intro x hx
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    subst x
    exact ⟨e.1, rfl⟩

/-- The expected r*m vertices survive with their original indices. -/
theorem card_cayleyComplex_vertices {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    (cayleyComplex z hz).vertices.ncard = r * m := by
  rw [cayleyComplex_vertices]
  simpa using Set.ncard_range_of_injective (cayleyPoint_injective_of_convexIndependent z hz)

/-- When there are at least two choices per color, every colorful face is proper. -/
theorem cayley_face_ne_whole_hull {r m D : ℕ} (hr : 0 < r) (hm : 2 ≤ m)
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k))) :
    convexHull ℝ S ≠ convexHull ℝ (Set.range (cayleyPoint z)) := by
  classical
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  let k : Fin r := ⟨0, hr⟩
  obtain ⟨j, hj⟩ := exists_ne (i k)
  have hxS : cayleyPoint z (k, j) ∉ S := by
    intro h
    obtain ⟨l, hl⟩ := hS h
    have he := cayleyPoint_injective_of_convexIndependent z hz hl
    have hkl : l = k := congrArg Prod.fst he
    have hji : i l = j := congrArg Prod.snd he
    exact hj (hkl ▸ hji.symm)
  obtain ⟨f, hf, hfS⟩ := exists_cayley_face_support z hz i S hS
  have he := convexHull_eq_zero_face _ S (Set.finite_range _)
    (subset_cayley_range_of_subset_corner z i S hS) f.toLinearMap hf hfS
  intro hwhole
  have hx : cayleyPoint z (k, j) ∈ convexHull ℝ S :=
    hwhole ▸ subset_convexHull ℝ _ (Set.mem_range_self (k, j))
  rw [he] at hx
  exact hxS ((hfS _ (Set.mem_range_self (k, j))).mp hx.2)

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.CayleyCentered` -/


/-!
# Nonvanishing centered differences of colorful Cayley combinations

Under a hypothetical convex-independent array, every colorful weight support
has a functional negative at the average of all Cayley generators. Disjoint
nonnegative colorful supports therefore give a nonzero centered difference.
The construction avoids relative boundaries and sphere homeomorphisms.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- An exact exposing functional for a weight support, strictly negative at the center.
The support can be empty; a full transversal still has an omitted generator. -/
theorem exists_cayley_weight_support {r m D : ℕ} (hr : 0 < r) (hm : 2 ≤ m)
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (a : (Fin r × Fin m) → ℝ) (i : Grid r m)
    (hi : ∀ e, a e ≠ 0 → e.2 = i e.1) :
    ∃ f : CayleySpace r D →L[ℝ] ℝ,
      (∀ e, f (cayleyPoint z e) ≤ 0) ∧
      (∀ e, f (cayleyPoint z e) = 0 ↔ a e ≠ 0) ∧
      f (finiteAverage (cayleyPoint z)) < 0 := by
  classical
  let S := cayleyPoint z '' {e | a e ≠ 0}
  have hinj := cayleyPoint_injective_of_convexIndependent z hz
  have hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k)) := by
    rintro x ⟨e, he, rfl⟩
    exact ⟨e.1, congrArg (cayleyPoint z) (Prod.ext rfl (hi e he).symm)⟩
  have hmem (e) : cayleyPoint z e ∈ S ↔ a e ≠ 0 := by
    constructor
    · rintro ⟨x, hx, hxe⟩
      rwa [hinj hxe] at hx
    · intro he
      exact ⟨e, he, rfl⟩
  obtain ⟨f, hf, hfS⟩ := exists_cayley_face_support z hz i S hS
  have hle (e) := hf _ (Set.mem_range_self e)
  have hiff (e) : f (cayleyPoint z e) = 0 ↔ a e ≠ 0 :=
    (hfS _ (Set.mem_range_self e)).trans (hmem e)
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  let k : Fin r := ⟨0, hr⟩
  obtain ⟨j, hj⟩ := exists_ne (i k)
  have haj : a (k, j) = 0 := by
    by_contra h
    exact hj (hi (k, j) h)
  have hneg : f (cayleyPoint z (k, j)) < 0 := lt_of_le_of_ne (hle _) (by
    intro heq
    exact (hiff (k, j)).mp heq haj)
  let : Nonempty (Fin r × Fin m) := ⟨(k, j)⟩
  exact ⟨f, hle, hiff, map_finiteAverage_neg _ f.toLinearMap hle ⟨(k, j), hneg⟩⟩

/-- The difference used in the planned odd-map construction. -/
noncomputable def cayleyCenteredDifference {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (a b : (Fin r × Fin m) → ℝ) : CayleySpace r D :=
  centeredCombination (cayleyPoint z) (finiteAverage (cayleyPoint z)) a -
    centeredCombination (cayleyPoint z) (finiteAverage (cayleyPoint z)) b

/-- Disjoint colorful nonnegative weights of positive total mass give a nonzero difference. -/
theorem cayleyCenteredDifference_ne_zero {r m D : ℕ} (hr : 0 < r) (hm : 2 ≤ m)
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (a b : (Fin r × Fin m) → ℝ) (i j : Grid r m)
    (hi : ∀ e, a e ≠ 0 → e.2 = i e.1) (hj : ∀ e, b e ≠ 0 → e.2 = j e.1)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hab : ∀ e, a e = 0 ∨ b e = 0)
    (hmass : 0 < (∑ e, a e) + ∑ e, b e) :
    cayleyCenteredDifference z a b ≠ 0 := by
  obtain ⟨f, hf, hfa, hfc⟩ := exists_cayley_weight_support hr hm z hz a i hi
  obtain ⟨g, hg, hgb, hgc⟩ := exists_cayley_weight_support hr hm z hz b j hj
  apply centeredCombination_sub_ne_zero _ _ a b f.toLinearMap g.toLinearMap
    hf hg hfc hgc ha hb (fun e he => (hfa e).mpr he) (fun e he => (hgb e).mpr he)
    (fun e he => ?_) hmass
  apply lt_of_le_of_ne (hf e)
  intro h
  exact (hfa e).mp h ((hab e).resolve_right he)

/-- Swapping the two coefficient families reverses the difference. -/
theorem cayleyCenteredDifference_swap {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (a b : (Fin r × Fin m) → ℝ) :
    cayleyCenteredDifference z b a = -cayleyCenteredDifference z a b := by
  simp [cayleyCenteredDifference]

/-- Continuous coefficient families give a continuous centered difference. -/
theorem continuous_cayleyCenteredDifference {X : Type*} [TopologicalSpace X] {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (a b : X → (Fin r × Fin m) → ℝ)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => cayleyCenteredDifference z (a x) (b x)) := by
  unfold cayleyCenteredDifference centeredCombination
  fun_prop

/-- The linear functional adding the color coordinates. -/
def cayleyColorSum (r D : ℕ) : CayleySpace r D →ₗ[ℝ] ℝ where
  toFun x := ∑ k, x.1 k
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

@[simp] theorem cayleyColorSum_point {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (e : Fin r × Fin m) :
    cayleyColorSum r D (cayleyPoint z e) = 1 := by
  simp [cayleyColorSum, cayleyPoint]

/-- The average remains on the affine hyperplane with color sum one. -/
theorem cayleyColorSum_average {r m D : ℕ} (hr : 0 < r) (hm : 0 < m)
    (z : Fin r → Fin m → Point D) :
    cayleyColorSum r D (finiteAverage (cayleyPoint z)) = 1 := by
  have hcard : (Fintype.card (Fin r × Fin m) : ℝ) ≠ 0 := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hr))
      (by exact_mod_cast (Nat.ne_of_gt hm))
  simp only [finiteAverage, map_smul, map_sum, cayleyColorSum_point,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact inv_mul_cancel₀ hcard

/-- Centering removes the color-sum coordinate, independently of the weights. -/
theorem cayleyColorSum_centeredCombination {r m D : ℕ} (hr : 0 < r) (hm : 0 < m)
    (z : Fin r → Fin m → Point D) (a : (Fin r × Fin m) → ℝ) :
    cayleyColorSum r D
      (centeredCombination (cayleyPoint z) (finiteAverage (cayleyPoint z)) a) = 0 := by
  rw [map_centeredCombination, cayleyColorSum_average hr hm]
  simp

/-- The entire difference lies in the kernel of the color-sum functional. -/
theorem cayleyCenteredDifference_mem_ker {r m D : ℕ} (hr : 0 < r) (hm : 0 < m)
    (z : Fin r → Fin m → Point D) (a b : (Fin r × Fin m) → ℝ) :
    cayleyCenteredDifference z a b ∈ LinearMap.ker (cayleyColorSum r D) := by
  rw [LinearMap.mem_ker]
  simp [cayleyCenteredDifference, cayleyColorSum_centeredCombination hr hm]

/-- A coefficient family supported at most once per color extends to a transversal.
The empty support is allowed, using the first vertex as the default choice. -/
theorem exists_transversal_of_colorful_weights {r m : ℕ} (hm : 0 < m)
    (a : (Fin r × Fin m) → ℝ)
    (ha : ∀ k j l, a (k, j) ≠ 0 → a (k, l) ≠ 0 → j = l) :
    ∃ i : Grid r m, ∀ e, a e ≠ 0 → e.2 = i e.1 := by
  classical
  let i : Grid r m := fun k => if h : ∃ j, a (k, j) ≠ 0 then h.choose else ⟨0, hm⟩
  refine ⟨i, ?_⟩
  rintro ⟨k, j⟩ hj
  have hex : ∃ l, a (k, l) ≠ 0 := ⟨j, hj⟩
  dsimp [i]
  rw [dite_eq_left hex]
  exact ha k j hex.choose hj hex.choose_spec

/-- A version ready for the hexagon coefficients, without preselected transversals. -/
theorem cayleyCenteredDifference_ne_zero_of_colorful {r m D : ℕ}
    (hr : 0 < r) (hm : 2 ≤ m)
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (a b : (Fin r × Fin m) → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hca : ∀ k j l, a (k, j) ≠ 0 → a (k, l) ≠ 0 → j = l)
    (hcb : ∀ k j l, b (k, j) ≠ 0 → b (k, l) ≠ 0 → j = l)
    (hab : ∀ e, a e = 0 ∨ b e = 0)
    (hmass : 0 < (∑ e, a e) + ∑ e, b e) :
    cayleyCenteredDifference z a b ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_transversal_of_colorful_weights (by omega : 0 < m) a hca
  obtain ⟨j, hj⟩ := exists_transversal_of_colorful_weights (by omega : 0 < m) b hcb
  exact cayleyCenteredDifference_ne_zero hr hm z hz a b i j hi hj ha hb hab hmass

/-- The color-sum kernel has codimension one as soon as a color exists. -/
theorem finrank_ker_cayleyColorSum_add_one {r D : ℕ} (hr : 0 < r) :
    Module.finrank ℝ (LinearMap.ker (cayleyColorSum r D)) + 1 = r + D := by
  have hf : cayleyColorSum r D ≠ 0 := by
    intro h
    have he := congrArg (fun f : CayleySpace r D →ₗ[ℝ] ℝ =>
      f (Pi.single (⟨0, hr⟩ : Fin r) 1, 0)) h
    simp [cayleyColorSum] at he
  simpa [CayleySpace, Point, Module.finrank_prod] using
    Module.Dual.finrank_ker_add_one_of_ne_zero hf

/-- In the required equal-dimension case, the target has dimension 2D-1. -/
theorem finrank_ker_cayleyColorSum (D : ℕ) (hD : 0 < D) :
    Module.finrank ℝ (LinearMap.ker (cayleyColorSum D D)) = 2 * D - 1 := by
  have h := finrank_ker_cayleyColorSum_add_one (D := D) hD
  omega

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonWeights` -/


/-!
# Explicit hexagon coefficients

The positive labels occupy alternating rays of the hexagon. The negative
coefficients are the same functions at the antipodal point. All claims are
for arbitrary real coordinates, including sector boundaries and the origin.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The three positive labels on rays (1,0), (0,-1), (-1,1). -/
noncomputable def hexWeight (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![max 0 (min p.1 (p.1 + p.2)),
    max 0 (min (-p.2) (-p.1 - p.2)),
    max 0 (min (-p.1) p.2)]

theorem hexWeight_nonneg (p : ℝ × ℝ) (j : Fin 3) : 0 ≤ hexWeight p j := by
  fin_cases j <;> simp [hexWeight]

/-- Among the three positive labels, at most one coefficient is nonzero. -/
theorem hexWeight_colorful (p : ℝ × ℝ) (i j : Fin 3)
    (hi : hexWeight p i ≠ 0) (hj : hexWeight p j ≠ 0) : i = j := by
  have hi' := lt_of_le_of_ne (hexWeight_nonneg p i) (Ne.symm hi)
  have hj' := lt_of_le_of_ne (hexWeight_nonneg p j) (Ne.symm hj)
  fin_cases i <;> fin_cases j <;>
    simp_all [hexWeight] <;> linarith

/-- A positive and a negative coefficient never use the same label. -/
theorem hexWeight_disjoint (p : ℝ × ℝ) (j : Fin 3) :
    hexWeight p j = 0 ∨ hexWeight (-p) j = 0 := by
  by_contra h
  push Not at h
  have ha := lt_of_le_of_ne (hexWeight_nonneg p j) (Ne.symm h.1)
  have hb := lt_of_le_of_ne (hexWeight_nonneg (-p) j) (Ne.symm h.2)
  fin_cases j <;> simp_all [hexWeight] <;> linarith

/-- The six coefficients vanish simultaneously only at the origin. -/
theorem eq_zero_of_hexWeight_eq_zero (p : ℝ × ℝ)
    (ha : ∀ j, hexWeight p j = 0) (hb : ∀ j, hexWeight (-p) j = 0) : p = 0 := by
  have hmin (u v : ℝ) (h : max 0 (min u v) = 0) : u ≤ 0 ∨ v ≤ 0 := by
    apply min_le_iff.mp
    exact (le_max_right 0 (min u v)).trans_eq h
  have ha0 := hmin p.1 (p.1 + p.2) (ha 0)
  have ha1 := hmin (-p.2) (-p.1 - p.2) (ha 1)
  have ha2 := hmin (-p.1) p.2 (ha 2)
  have hb0 := hmin (-p.1) (-p.1 + -p.2) (hb 0)
  have hb1 := hmin (-(-p.2)) (-(-p.1) - -p.2) (hb 1)
  have hb2 := hmin (-(-p.1)) (-p.2) (hb 2)
  have hxl : p.1 ≤ 0 := by
    rcases ha0 with h | h <;> rcases hb2 with h' | h' <;> linarith
  have hxr : 0 ≤ p.1 := by
    rcases hb0 with h | h <;> rcases ha2 with h' | h' <;> linarith
  apply Prod.ext
  · exact le_antisymm hxl hxr
  · change p.2 = 0
    rcases ha1 with h | h <;> rcases hb1 with h' | h' <;> linarith

/-- The coefficients are continuous across all sector boundaries. -/
theorem continuous_hexWeight : Continuous hexWeight := by
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp [hexWeight] <;> fun_prop

@[simp] theorem hexWeight_zero (j : Fin 3) : hexWeight 0 j = 0 := by
  fin_cases j <;> norm_num [hexWeight]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonMap` -/


/-!
# The continuous odd map produced by a hypothetical Sanyal counterexample

One hexagon per color supplies disjoint colorful weights. Their centered
Cayley difference is nonzero off the origin and takes values in a space of
dimension 2D-1. The topological assertion forbidding this map is not proved here.
-/

namespace VCDimConvexBound

open scoped BigOperators

abbrev HexagonDomain (r : ℕ) := Fin r → ℝ × ℝ

/-- Apply the three hexagon weights independently in each color. -/
noncomputable def hexCoeffs {r : ℕ} (x : HexagonDomain r) (e : Fin r × Fin 3) : ℝ :=
  hexWeight (x e.1) e.2

theorem continuous_hexCoeffs (r : ℕ) : Continuous (@hexCoeffs r) := by
  apply continuous_pi
  intro e
  exact ((continuous_apply e.2).comp continuous_hexWeight).comp (continuous_apply e.1)

/-- A nonzero input has positive total mass among the two coefficient families. -/
theorem hexCoeffs_total_pos {r : ℕ} (x : HexagonDomain r) (hx : x ≠ 0) :
    0 < (∑ e, hexCoeffs x e) + ∑ e, hexCoeffs (-x) e := by
  have ha : 0 ≤ ∑ e, hexCoeffs x e :=
    Finset.sum_nonneg (fun e _ => hexWeight_nonneg _ _)
  have hb : 0 ≤ ∑ e, hexCoeffs (-x) e :=
    Finset.sum_nonneg (fun e _ => hexWeight_nonneg _ _)
  by_contra hn
  have hle := le_of_not_gt hn
  have hsa : ∑ e, hexCoeffs x e = 0 := by linarith
  have hsb : ∑ e, hexCoeffs (-x) e = 0 := by linarith
  have hza := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => hexWeight_nonneg (x e.1) e.2)).mp hsa
  have hzb := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => hexWeight_nonneg ((-x) e.1) e.2)).mp hsb
  apply hx
  funext k
  exact eq_zero_of_hexWeight_eq_zero (x k)
    (fun j => hza (k, j) (Finset.mem_univ _)) (fun j => hzb (k, j) (Finset.mem_univ _))

/-- The concrete map into the ambient Cayley space. -/
noncomputable def hexagonCayleyMap {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (x : HexagonDomain r) : CayleySpace r D :=
  cayleyCenteredDifference z (hexCoeffs x) (hexCoeffs (-x))

theorem continuous_hexagonCayleyMap {r D : ℕ} (z : Fin r → Fin 3 → Point D) :
    Continuous (hexagonCayleyMap z) := by
  exact continuous_cayleyCenteredDifference z _ _ (continuous_hexCoeffs r)
    ((continuous_hexCoeffs r).comp continuous_neg)

theorem hexagonCayleyMap_neg {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (x : HexagonDomain r) : hexagonCayleyMap z (-x) = -hexagonCayleyMap z x := by
  simp only [hexagonCayleyMap, neg_neg]
  exact cayleyCenteredDifference_swap z _ _

/-- All combinatorial hypotheses of the centered-difference theorem are now supplied. -/
theorem hexagonCayleyMap_ne_zero {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (x : HexagonDomain r) (hx : x ≠ 0) : hexagonCayleyMap z x ≠ 0 := by
  exact cayleyCenteredDifference_ne_zero_of_colorful hr (by decide) z hz _ _
    (fun e => hexWeight_nonneg _ _) (fun e => hexWeight_nonneg _ _)
    (fun k j l => hexWeight_colorful (x k) j l)
    (fun k j l => hexWeight_colorful ((-x) k) j l)
    (fun e => hexWeight_disjoint (x e.1) e.2) (hexCoeffs_total_pos x hx)

/-- The actual target is the color-sum kernel, rather than the larger ambient space. -/
noncomputable def hexagonKernelMap {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (x : HexagonDomain r) :
    LinearMap.ker (cayleyColorSum r D) :=
  ⟨hexagonCayleyMap z x, cayleyCenteredDifference_mem_ker hr (by decide) z _ _⟩

theorem continuous_hexagonKernelMap {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) : Continuous (hexagonKernelMap hr z) :=
  (continuous_hexagonCayleyMap z).subtype_mk _

theorem hexagonKernelMap_neg {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (x : HexagonDomain r) :
    hexagonKernelMap hr z (-x) = -hexagonKernelMap hr z x := by
  apply Subtype.ext
  exact hexagonCayleyMap_neg z x

theorem hexagonKernelMap_ne_zero {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (x : HexagonDomain r) (hx : x ≠ 0) : hexagonKernelMap hr z x ≠ 0 := by
  intro h
  exact hexagonCayleyMap_ne_zero hr z hz x hx (congrArg Subtype.val h)

/-- There are exactly two real input coordinates per color. -/
theorem finrank_hexagonDomain (r : ℕ) : Module.finrank ℝ (HexagonDomain r) = 2 * r := by
  simp [HexagonDomain, Module.finrank_pi_fintype, Module.finrank_prod, Nat.mul_comm]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonFan` -/


/-!
# Six closed linear sectors of the hexagon

Each sector is the image of the nonnegative quadrant under an invertible
linear map. The six sectors cover the whole plane, including their boundaries.
On each sector, the signed hexagon coefficients are a fixed linear function.
-/

namespace VCDimConvexBound

/-- Coordinates in consecutive pairs of hexagon rays, in counterclockwise order. -/
def hexSectorMap (s : Fin 6) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := ![p, (-p.2, p.1 + p.2), (-p.1 - p.2, p.1),
    (-p.1, -p.2), (p.2, -p.1 - p.2), (p.1 + p.2, -p.1)] s
  map_add' p q := by fin_cases s <;> ext <;> simp <;> ring
  map_smul' a p := by fin_cases s <;> ext <;> simp <;> ring

/-- Every sector parameterization is injective, even outside the nonnegative quadrant. -/
theorem hexSectorMap_injective (s : Fin 6) : Function.Injective (hexSectorMap s) := by
  intro p q h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  fin_cases s <;> simp [hexSectorMap] at h₁ h₂ <;> apply Prod.ext <;> linarith

/-- The six closed sectors cover the plane; overlapping boundary choices are allowed. -/
theorem exists_hexSector (p : ℝ × ℝ) :
    ∃ s : Fin 6, ∃ t : ℝ × ℝ, 0 ≤ t.1 ∧ 0 ≤ t.2 ∧ hexSectorMap s t = p := by
  rcases le_total 0 p.1 with hx | hx <;> rcases le_total 0 p.2 with hy | hy
  · exact ⟨0, p, hx, hy, rfl⟩
  · by_cases hs : 0 ≤ p.1 + p.2
    · refine ⟨5, (-p.2, p.1 + p.2), by linarith, hs, ?_⟩
      ext <;> simp [hexSectorMap]
    · refine ⟨4, (-p.1 - p.2, p.1), by linarith, hx, ?_⟩
      ext <;> simp [hexSectorMap]
  · by_cases hs : 0 ≤ p.1 + p.2
    · refine ⟨1, (p.1 + p.2, -p.1), hs, by linarith, ?_⟩
      ext <;> simp [hexSectorMap]
    · refine ⟨2, (p.2, -p.1 - p.2), hy, by linarith, ?_⟩
      ext <;> simp [hexSectorMap]
      ring
  · refine ⟨3, (-p.1, -p.2), by linarith, by linarith, ?_⟩
    ext <;> simp [hexSectorMap]

/-- On each sector, the three signed label coefficients are linear in its two parameters. -/
def hexSectorWeight (s : Fin 6) : (ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun p := ![![p.1, -p.2, 0], ![0, -p.1, p.2], ![-p.2, 0, p.1],
    ![-p.1, p.2, 0], ![0, p.1, -p.2], ![p.2, 0, -p.1]] s
  map_add' p q := by
    fin_cases s <;> funext j <;> fin_cases j <;> simp <;> ring
  map_smul' a p := by
    fin_cases s <;> funext j <;> fin_cases j <;> simp

/-- This is an equality with the actual min/max coefficients, not a new model. -/
theorem hexWeight_sub_eq_sector (s : Fin 6) (t : ℝ × ℝ)
    (ha : 0 ≤ t.1) (hb : 0 ≤ t.2) (j : Fin 3) :
    hexWeight (hexSectorMap s t) j - hexWeight (-hexSectorMap s t) j =
      hexSectorWeight s t j := by
  fin_cases s <;> fin_cases j <;>
    simp [hexWeight, hexSectorMap, hexSectorWeight] <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- Nonnegative coordinates in the product of sector parameter spaces. -/
def HexNonnegative {r : ℕ} (t : HexagonDomain r) : Prop :=
  ∀ k, 0 ≤ (t k).1 ∧ 0 ≤ (t k).2

/-- Choose one of six sectors independently for each color. -/
def hexSectorArray {r : ℕ} (s : Fin r → Fin 6) : HexagonDomain r →ₗ[ℝ] HexagonDomain r where
  toFun t k := hexSectorMap (s k) (t k)
  map_add' t u := by funext k; exact map_add _ _ _
  map_smul' a t := by
    funext k
    exact (hexSectorMap (s k)).map_smul a (t k)

theorem hexSectorArray_injective {r : ℕ} (s : Fin r → Fin 6) :
    Function.Injective (hexSectorArray s) := by
  intro t u h
  funext k
  exact hexSectorMap_injective (s k) (congrFun h k)

/-- Product sectors cover every input, not merely points in general position. -/
theorem exists_hexSectorArray {r : ℕ} (x : HexagonDomain r) :
    ∃ s : Fin r → Fin 6, ∃ t, HexNonnegative t ∧ hexSectorArray s t = x := by
  choose s t ht₁ ht₂ he using fun k => exists_hexSector (x k)
  exact ⟨s, t, fun k => ⟨ht₁ k, ht₂ k⟩, funext he⟩

theorem card_hexSectorArrays (r : ℕ) : Fintype.card (Fin r → Fin 6) = 6 ^ r := by
  simp

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonLinearPieces` -/


/-!
# Linear pieces and normalized kernel certificates

The actual hexagon map agrees with one of 6^r linear maps on each closed
product sector. A non-origin zero is equivalent to a nonnegative kernel
vector of total coordinate mass one in one of these finitely many pieces.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The linear extension of a fixed piece to all sector coordinates. -/
noncomputable def hexPieceLinear {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) : HexagonDomain r →ₗ[ℝ] CayleySpace r D where
  toFun t := ∑ e : Fin r × Fin 3, hexSectorWeight (s e.1) (t e.1) e.2 •
    (cayleyPoint z e - finiteAverage (cayleyPoint z))
  map_add' t u := by simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [map_smul, mul_smul, Finset.smul_sum]

/-- Each linear piece is the original map on its closed product sector. -/
theorem hexagonCayleyMap_sector {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (t : HexagonDomain r) (ht : HexNonnegative t) :
    hexagonCayleyMap z (hexSectorArray s t) = hexPieceLinear z s t := by
  change (∑ e, hexWeight (hexSectorMap (s e.1) (t e.1)) e.2 •
    (cayleyPoint z e - finiteAverage (cayleyPoint z))) -
    (∑ e, hexWeight (-hexSectorMap (s e.1) (t e.1)) e.2 •
    (cayleyPoint z e - finiteAverage (cayleyPoint z))) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← sub_smul, hexWeight_sub_eq_sector _ _ (ht e.1).1 (ht e.1).2]

/-- A piece lands in the color-sum kernel even outside its defining nonnegative sector. -/
theorem hexPieceLinear_mem_ker {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (s : Fin r → Fin 6) (t : HexagonDomain r) :
    hexPieceLinear z s t ∈ LinearMap.ker (cayleyColorSum r D) := by
  rw [LinearMap.mem_ker]
  exact cayleyColorSum_centeredCombination hr (by decide) z
    (fun e => hexSectorWeight (s e.1) (t e.1) e.2)

/-- Regard a piece as a linear map into the correct lower-dimensional space. -/
noncomputable def hexPieceKernelLinear {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (s : Fin r → Fin 6) :
    HexagonDomain r →ₗ[ℝ] LinearMap.ker (cayleyColorSum r D) :=
  LinearMap.codRestrict _ (hexPieceLinear z s) (hexPieceLinear_mem_ker hr z s)

/-- Rank-nullity supplies a nonzero kernel vector in every piece.
This does not say that the vector belongs to the nonnegative sector. -/
theorem exists_ne_zero_hexPiece_kernel (D : ℕ) (hD : 0 < D)
    (z : Fin D → Fin 3 → Point D) (s : Fin D → Fin 6) :
    ∃ t : HexagonDomain D, t ≠ 0 ∧ hexPieceLinear z s t = 0 := by
  have hdim : Module.finrank ℝ (LinearMap.ker (cayleyColorSum D D)) <
      Module.finrank ℝ (HexagonDomain D) := by
    rw [finrank_ker_cayleyColorSum D hD, finrank_hexagonDomain]
    omega
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := hexPieceKernelLinear hD z s) hdim
  obtain ⟨t, ht, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨t, hn, congrArg Subtype.val (LinearMap.mem_ker.mp ht)⟩

/-- The mass used to normalize nonnegative sector coordinates. -/
def hexParameterMass {r : ℕ} : HexagonDomain r →ₗ[ℝ] ℝ where
  toFun t := ∑ k, ((t k).1 + (t k).2)
  map_add' t u := by
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  map_smul' a t := by
    simp [smul_eq_mul, mul_add, Finset.mul_sum]

/-- Nonnegative coordinates have positive mass unless all coordinates vanish. -/
theorem hexParameterMass_pos {r : ℕ} (t : HexagonDomain r)
    (ht : HexNonnegative t) (hn : t ≠ 0) : 0 < hexParameterMass t := by
  have hnonneg : ∀ k, 0 ≤ (t k).1 + (t k).2 := fun k => add_nonneg (ht k).1 (ht k).2
  have hs : 0 ≤ hexParameterMass t := by
    change 0 ≤ ∑ k, ((t k).1 + (t k).2)
    exact Finset.sum_nonneg (fun k _ => hnonneg k)
  by_contra h
  have heq : hexParameterMass t = 0 := le_antisymm (le_of_not_gt h) hs
  change (∑ k, ((t k).1 + (t k).2)) = 0 at heq
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg k)).mp heq
  apply hn
  funext k
  have h₀ := hk k (Finset.mem_univ k)
  have h₁ := (ht k).1
  have h₂ := (ht k).2
  apply Prod.ext <;> change _ = 0 <;> linarith

theorem HexNonnegative.smul {r : ℕ} {t : HexagonDomain r} (ht : HexNonnegative t)
    {a : ℝ} (ha : 0 ≤ a) : HexNonnegative (a • t) := by
  intro k
  exact ⟨mul_nonneg ha (ht k).1, mul_nonneg ha (ht k).2⟩

/-- A zero of the nonlinear formula is exactly a normalized nonnegative kernel certificate. -/
theorem hexagon_zero_iff_normalized_piece_kernel {r D : ℕ}
    (z : Fin r → Fin 3 → Point D) :
    (∃ x : HexagonDomain r, x ≠ 0 ∧ hexagonCayleyMap z x = 0) ↔
      ∃ s : Fin r → Fin 6, ∃ t : HexagonDomain r,
        HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0 := by
  constructor
  · rintro ⟨x, hx, hz⟩
    obtain ⟨s, t, ht, he⟩ := exists_hexSectorArray x
    have hn : t ≠ 0 := by
      intro h
      rw [h, map_zero] at he
      exact hx he.symm
    have hm := hexParameterMass_pos t ht hn
    have hk : hexPieceLinear z s t = 0 := by
      rw [← hexagonCayleyMap_sector z s t ht, he]
      exact hz
    refine ⟨s, (hexParameterMass t)⁻¹ • t,
      ht.smul (inv_nonneg.mpr hm.le), ?_, ?_⟩
    · simp [map_smul, smul_eq_mul, ne_of_gt hm]
    · simp [map_smul, hk]
  · rintro ⟨s, t, ht, hm, hz⟩
    have hn : t ≠ 0 := by
      intro h
      simp [h] at hm
    refine ⟨hexSectorArray s t, ?_, ?_⟩
    · intro h
      apply hn
      apply hexSectorArray_injective s
      simpa using h
    · rw [hexagonCayleyMap_sector z s t ht]
      exact hz

/-- Nonnegative scaling preserves sectors and commutes with the concrete map. -/
theorem hexagonCayleyMap_nonneg_smul {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (x : HexagonDomain r) (a : ℝ) (ha : 0 ≤ a) :
    hexagonCayleyMap z (a • x) = a • hexagonCayleyMap z x := by
  obtain ⟨s, t, ht, rfl⟩ := exists_hexSectorArray x
  rw [← map_smul, hexagonCayleyMap_sector z s (a • t) (ht.smul ha),
    map_smul, hexagonCayleyMap_sector z s t ht]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonSymmetry` -/


/-!
# Adjacent sectors and the antipodal symmetry

The six-sector presentation comes with explicit boundary identifications and
an involution without fixed sectors. The opposite linear pieces are negatives
on the same coordinates; normalized kernel certificates occur in pairs.
-/

namespace VCDimConvexBound

/-- The next sector in cyclic order. -/
def hexNext (s : Fin 6) : Fin 6 := s + 1

/-- The antipodal sector, three steps further around the hexagon. -/
def hexOpposite (s : Fin 6) : Fin 6 := s + 3

theorem hexOpposite_involutive : Function.Involutive hexOpposite := by
  intro s
  fin_cases s <;> decide

theorem hexOpposite_ne_self (s : Fin 6) : hexOpposite s ≠ s := by
  fin_cases s <;> decide

theorem hexOpposite_next (s : Fin 6) : hexOpposite (hexNext s) = hexNext (hexOpposite s) := by
  fin_cases s <;> decide

/-- The outgoing ray of a sector is the incoming ray of the next one. -/
theorem hexSectorMap_boundary (s : Fin 6) (a : ℝ) :
    hexSectorMap s (0, a) = hexSectorMap (hexNext s) (a, 0) := by
  fin_cases s <;> ext <;> simp [hexNext, hexSectorMap]

/-- Adjacent closed sectors meet exactly in their common ray. -/
theorem hexSectorMap_adjacent_eq_iff (s : Fin 6) (u v : ℝ × ℝ)
    (hu : 0 ≤ u.1 ∧ 0 ≤ u.2) (hv : 0 ≤ v.1 ∧ 0 ≤ v.2) :
    hexSectorMap s u = hexSectorMap (hexNext s) v ↔
      u.1 = 0 ∧ v.2 = 0 ∧ u.2 = v.1 := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    fin_cases s <;> simp [hexNext, hexSectorMap] at h₁ h₂ <;>
      refine ⟨?_, ?_, ?_⟩ <;> linarith [hu.1, hu.2, hv.1, hv.2]
  · rintro ⟨ha, hb, hc⟩
    have hu' : u = (0, u.2) := Prod.ext ha rfl
    have hv' : v = (u.2, 0) := Prod.ext hc.symm hb
    rw [hu', hv', hexSectorMap_boundary]

/-- Opposite sectors represent opposite points with unchanged parameters. -/
theorem hexSectorMap_opposite (s : Fin 6) (t : ℝ × ℝ) :
    hexSectorMap (hexOpposite s) t = -hexSectorMap s t := by
  fin_cases s <;> ext <;> simp [hexOpposite, hexSectorMap] <;> ring

/-- The linear coefficient vectors on opposite sectors negate one another. -/
theorem hexSectorWeight_opposite (s : Fin 6) (t : ℝ × ℝ) :
    hexSectorWeight (hexOpposite s) t = -hexSectorWeight s t := by
  fin_cases s <;> funext j <;> fin_cases j <;> simp [hexOpposite, hexSectorWeight]

/-- The product-sector involution realizes the antipodal action on the domain. -/
theorem hexSectorArray_opposite {r : ℕ} (s : Fin r → Fin 6) (t : HexagonDomain r) :
    hexSectorArray (hexOpposite ∘ s) t = -hexSectorArray s t := by
  funext k
  exact hexSectorMap_opposite (s k) (t k)

/-- Opposite extensions have the same kernel, without a nonnegativity assumption. -/
theorem hexPieceLinear_opposite {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (t : HexagonDomain r) :
    hexPieceLinear z (hexOpposite ∘ s) t = -hexPieceLinear z s t := by
  simp [hexPieceLinear, hexSectorWeight_opposite, Finset.sum_neg_distrib]

theorem hexPieceLinear_opposite_eq_zero_iff {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (t : HexagonDomain r) :
    hexPieceLinear z (hexOpposite ∘ s) t = 0 ↔ hexPieceLinear z s t = 0 := by
  rw [hexPieceLinear_opposite, neg_eq_zero]

/-- Every certificate has an antipodal partner with exactly the same coordinates. -/
theorem hex_normalized_kernel_opposite_iff {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (t : HexagonDomain r) :
    (HexNonnegative t ∧ hexParameterMass t = 1 ∧
      hexPieceLinear z (hexOpposite ∘ s) t = 0) ↔
    (HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0) := by
  rw [hexPieceLinear_opposite_eq_zero_iff]

/-- Exactly one of a sector and its opposite lies in the first three sectors. -/
theorem hexOpposite_lt_three_iff (s : Fin 6) :
    (hexOpposite s).val < 3 ↔ 3 ≤ s.val := by
  fin_cases s <;> decide

/-- It suffices to search one representative of each antipodal pair.
The choice is global: all sectors are negated together, not independently. -/
theorem exists_hex_normalized_kernel_first_half_iff {r D : ℕ}
    (z : Fin r → Fin 3 → Point D) (k : Fin r) :
    (∃ s : Fin r → Fin 6, ∃ t : HexagonDomain r,
      HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0) ↔
    (∃ s : Fin r → Fin 6, ∃ t : HexagonDomain r,
      (s k).val < 3 ∧ HexNonnegative t ∧ hexParameterMass t = 1 ∧
        hexPieceLinear z s t = 0) := by
  constructor
  · rintro ⟨s, t, ht, hm, hz⟩
    by_cases hs : (s k).val < 3
    · exact ⟨s, t, hs, ht, hm, hz⟩
    · refine ⟨hexOpposite ∘ s, t, ?_, ht, hm, ?_⟩
      · exact (hexOpposite_lt_three_iff (s k)).mpr (by omega)
      · rw [hexPieceLinear_opposite, hz, neg_zero]
  · rintro ⟨s, t, _, ht, hm, hz⟩
    exact ⟨s, t, ht, hm, hz⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonGluing` -/


/-!
# Compatibility of normalized sector certificates on overlaps

The hexagonal radius recovers the sum of nonnegative sector coordinates,
independently of the sector chosen. Thus both the linear map and the mass-one
normalization agree on overlaps. Updating a boundary coordinate gives an
explicit move to an adjacent product sector that preserves certificates.
-/

namespace VCDimConvexBound

/-- A coordinate-independent radius for the unit hexagon. -/
noncomputable def hexRadius (p : ℝ × ℝ) : ℝ :=
  max |p.1| (max |p.2| |p.1 + p.2|)

/-- On any nonnegative sector, radius is exactly coordinate mass. -/
theorem hexRadius_sector (s : Fin 6) (t : ℝ × ℝ)
    (ht : 0 ≤ t.1 ∧ 0 ≤ t.2) : hexRadius (hexSectorMap s t) = t.1 + t.2 := by
  fin_cases s <;> simp [hexRadius, hexSectorMap] <;>
    simp only [abs_eq_max_neg, max_def] <;> split_ifs <;> linarith [ht.1, ht.2]

/-- The sector-coordinate mass does not depend on the presentation of a point. -/
theorem hexSectorMass_eq_of_eq (s s' : Fin 6) (t u : ℝ × ℝ)
    (ht : 0 ≤ t.1 ∧ 0 ≤ t.2) (hu : 0 ≤ u.1 ∧ 0 ≤ u.2)
    (he : hexSectorMap s t = hexSectorMap s' u) : t.1 + t.2 = u.1 + u.2 := by
  rw [← hexRadius_sector s t ht, ← hexRadius_sector s' u hu, he]

/-- All product-sector overlaps, including higher-codimension ones, preserve mass. -/
theorem hexParameterMass_eq_of_sectorArray_eq {r : ℕ}
    (s s' : Fin r → Fin 6) (t u : HexagonDomain r)
    (ht : HexNonnegative t) (hu : HexNonnegative u)
    (he : hexSectorArray s t = hexSectorArray s' u) :
    hexParameterMass t = hexParameterMass u := by
  change (∑ k, ((t k).1 + (t k).2)) = ∑ k, ((u k).1 + (u k).2)
  apply Finset.sum_congr rfl
  intro k _
  exact hexSectorMass_eq_of_eq (s k) (s' k) (t k) (u k) (ht k) (hu k) (congrFun he k)

/-- Linear pieces agree wherever their nonnegative sector images overlap. -/
theorem hexPieceLinear_eq_of_sectorArray_eq {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s s' : Fin r → Fin 6) (t u : HexagonDomain r)
    (ht : HexNonnegative t) (hu : HexNonnegative u)
    (he : hexSectorArray s t = hexSectorArray s' u) :
    hexPieceLinear z s t = hexPieceLinear z s' u := by
  rw [← hexagonCayleyMap_sector z s t ht, ← hexagonCayleyMap_sector z s' u hu, he]

/-- Normalized zero certificates are independent of the chosen sector coordinates. -/
theorem hex_normalized_kernel_overlap_iff {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s s' : Fin r → Fin 6) (t u : HexagonDomain r)
    (ht : HexNonnegative t) (hu : HexNonnegative u)
    (he : hexSectorArray s t = hexSectorArray s' u) :
    (hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0) ↔
      (hexParameterMass u = 1 ∧ hexPieceLinear z s' u = 0) := by
  rw [hexParameterMass_eq_of_sectorArray_eq s s' t u ht hu he,
    hexPieceLinear_eq_of_sectorArray_eq z s s' t u ht hu he]

/-- Move one boundary coordinate to the next sector without changing its point. -/
theorem hexSectorArray_boundary_update {r : ℕ} (s : Fin r → Fin 6)
    (t : HexagonDomain r) (k : Fin r) (hk : (t k).1 = 0) :
    hexSectorArray (Function.update s k (hexNext (s k)))
      (Function.update t k ((t k).2, 0)) = hexSectorArray s t := by
  funext j
  by_cases hj : j = k
  · subst j
    simp only [hexSectorArray, LinearMap.coe_mk, AddHom.coe_mk, Function.update_self]
    have ht : t k = (0, (t k).2) := Prod.ext hk rfl
    conv_rhs => rw [ht]
    exact (hexSectorMap_boundary (s k) (t k).2).symm
  · simp [hexSectorArray, Function.update_of_ne hj]

/-- The explicit boundary move keeps all coordinates nonnegative. -/
theorem HexNonnegative.boundary_update {r : ℕ} {t : HexagonDomain r}
    (ht : HexNonnegative t) (k : Fin r) :
    HexNonnegative (Function.update t k ((t k).2, 0)) := by
  intro j
  by_cases hj : j = k
  · subst j
    simpa using And.intro (ht k).2 (le_refl (0 : ℝ))
  · simpa [Function.update_of_ne hj] using ht j

/-- A normalized kernel certificate passes across any available boundary face. -/
theorem hex_normalized_kernel_boundary_update {r D : ℕ}
    (z : Fin r → Fin 3 → Point D) (s : Fin r → Fin 6) (t : HexagonDomain r)
    (ht : HexNonnegative t) (hm : hexParameterMass t = 1)
    (hz : hexPieceLinear z s t = 0) (k : Fin r) (hk : (t k).1 = 0) :
    HexNonnegative (Function.update t k ((t k).2, 0)) ∧
      hexParameterMass (Function.update t k ((t k).2, 0)) = 1 ∧
      hexPieceLinear z (Function.update s k (hexNext (s k)))
        (Function.update t k ((t k).2, 0)) = 0 := by
  have hu := ht.boundary_update k
  refine ⟨hu, ?_⟩
  exact (hex_normalized_kernel_overlap_iff z _ _ _ _ hu ht
    (hexSectorArray_boundary_update s t k hk)).mpr ⟨hm, hz⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonComplex` -/


/-!
# The finite complex underlying the normalized hexagon fan

A facet chooses an edge of the six-cycle in every color. Its 2r vertices are
indexed without repetition by `Fin r × Bool`. All nonempty subsets of these
facets form an abstract simplicial complex, the join of r six-cycles.
-/

namespace VCDimConvexBound

/-- The predecessor in cyclic order. -/
def hexPrev (s : Fin 6) : Fin 6 := s + 5

theorem hexNext_ne_self (s : Fin 6) : hexNext s ≠ s := by
  fin_cases s <;> decide

theorem hexPrev_next (s : Fin 6) : hexPrev (hexNext s) = s := by
  fin_cases s <;> decide

theorem hexNext_prev (s : Fin 6) : hexNext (hexPrev s) = s := by
  fin_cases s <;> decide

abbrev HexVertex (r : ℕ) := Fin r × Fin 6

/-- The two endpoints of the chosen edge in each color. -/
def hexFacetVertex {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) : HexVertex r :=
  (e.1, if e.2 then hexNext (s e.1) else s e.1)

theorem hexFacetVertex_injective {r : ℕ} (s : Fin r → Fin 6) :
    Function.Injective (hexFacetVertex s) := by
  rintro ⟨k, b⟩ ⟨l, c⟩ h
  have hkl : k = l := congrArg Prod.fst h
  subst l
  have hbc := congrArg Prod.snd h
  cases b <;> cases c <;> simp [hexFacetVertex] at hbc ⊢
  · exact (hexNext_ne_self (s k) hbc.symm).elim
  · exact (hexNext_ne_self (s k) hbc).elim

/-- The vertex set of a maximal simplex of the join of six-cycles. -/
def hexFacet {r : ℕ} (s : Fin r → Fin 6) : Finset (HexVertex r) :=
  Finset.univ.image (hexFacetVertex s)

theorem mem_hexFacet {r : ℕ} (s : Fin r → Fin 6) (v : HexVertex r) :
    v ∈ hexFacet s ↔ v.2 = s v.1 ∨ v.2 = hexNext (s v.1) := by
  rcases v with ⟨k, j⟩
  constructor
  · intro hv
    obtain ⟨⟨l, b⟩, _, he⟩ := Finset.mem_image.mp hv
    have hl : l = k := congrArg Prod.fst he
    subst l
    have hj := congrArg Prod.snd he
    cases b
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
  · rintro (hj | hj)
    · exact Finset.mem_image.mpr ⟨(k, false), Finset.mem_univ _, Prod.ext rfl hj.symm⟩
    · exact Finset.mem_image.mpr ⟨(k, true), Finset.mem_univ _, Prod.ext rfl hj.symm⟩

theorem card_hexFacet {r : ℕ} (s : Fin r → Fin 6) : (hexFacet s).card = 2 * r := by
  rw [hexFacet, Finset.card_image_of_injective _ (hexFacetVertex_injective s)]
  simp [Nat.mul_comm]

theorem hexFacetVertex_mem {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) :
    hexFacetVertex s e ∈ hexFacet s :=
  Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

/-- The nonempty subsets of the facets form the finite domain complex. -/
def hexFanComplex (r : ℕ) : AbstractSimplicialComplex (HexVertex r) where
  faces := {t | t.Nonempty ∧ ∃ s : Fin r → Fin 6, t ⊆ hexFacet s}
  isRelLowerSet_faces := by
    rintro t ⟨ht, s, hs⟩
    refine ⟨ht, ?_⟩
    intro u hut hu
    exact ⟨hu, s, hut.trans hs⟩
  singleton_mem := by
    intro v
    refine ⟨Finset.singleton_nonempty v, (fun _ => v.2), ?_⟩
    rw [Finset.singleton_subset_iff, mem_hexFacet]
    exact Or.inl rfl

theorem hexFacet_mem_faces {r : ℕ} (hr : 0 < r) (s : Fin r → Fin 6) :
    hexFacet s ∈ (hexFanComplex r).faces := by
  refine ⟨?_, s, Finset.Subset.refl _⟩
  exact ⟨hexFacetVertex s (⟨0, hr⟩, false), hexFacetVertex_mem s _⟩

/-- Every face has at most 2r vertices; facets attain this number. -/
theorem card_le_of_mem_hexFanComplex {r : ℕ} (t : Finset (HexVertex r))
    (ht : t ∈ (hexFanComplex r).faces) : t.card ≤ 2 * r := by
  obtain ⟨_, s, hs⟩ := ht
  exact (Finset.card_le_card hs).trans_eq (card_hexFacet s)

/-- Removing one vertex gives the codimension-one boundary face of a facet. -/
def hexRidge {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) : Finset (HexVertex r) :=
  (hexFacet s).erase (hexFacetVertex s e)

theorem card_hexRidge {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) :
    (hexRidge s e).card + 1 = 2 * r := by
  rw [hexRidge, Finset.card_erase_add_one (hexFacetVertex_mem s e), card_hexFacet]

/-- A ridge retains the other endpoint in the deleted vertex's color. -/
theorem mem_hexRidge {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) (v : HexVertex r) :
    v ∈ hexRidge s e ↔
      if v.1 = e.1 then v.2 = (if e.2 then s e.1 else hexNext (s e.1))
      else v ∈ hexFacet s := by
  rw [hexRidge, Finset.mem_erase, mem_hexFacet]
  by_cases h : v.1 = e.1
  · rw [ite_eq_left h]
    rcases v with ⟨k, j⟩
    rcases e with ⟨l, b⟩
    dsimp at h
    subst k
    have hn := hexNext_ne_self (s l)
    cases b
    · change ((l, j) ≠ (l, s l) ∧ (j = s l ∨ j = hexNext (s l))) ↔ j = hexNext (s l)
      simp only [ne_eq, Prod.mk.injEq, true_and]
      constructor
      · rintro ⟨hne, he | he⟩
        · exact (hne he).elim
        · exact he
      · intro he
        refine ⟨?_, Or.inr he⟩
        intro ha
        exact hn (he.symm.trans ha)
    · change ((l, j) ≠ (l, hexNext (s l)) ∧ (j = s l ∨ j = hexNext (s l))) ↔ j = s l
      simp only [ne_eq, Prod.mk.injEq, true_and]
      constructor
      · rintro ⟨hne, he | he⟩
        · exact he
        · exact (hne he).elim
      · intro he
        refine ⟨?_, Or.inl he⟩
        intro hb
        exact hn (hb.symm.trans he)
  · rw [ite_eq_right h]
    have hn : v ≠ hexFacetVertex s e := by
      intro he
      exact h (congrArg Prod.fst he)
    simp [hn]

/-- Distinct sector assignments give distinct facets. -/
theorem hexFacet_injective (r : ℕ) : Function.Injective (@hexFacet r) := by
  have hedge : ∀ a b : Fin 6,
      (∀ j, (j = a ∨ j = hexNext a) ↔ (j = b ∨ j = hexNext b)) → a = b := by decide
  intro s t h
  funext k
  apply hedge
  intro j
  rw [← mem_hexFacet s (k, j), h, mem_hexFacet t (k, j)]

/-- Antipodal action on the vertices of the domain complex. -/
def hexVertexOpposite {r : ℕ} (v : HexVertex r) : HexVertex r :=
  (v.1, hexOpposite v.2)

theorem hexVertexOpposite_mem_facet_iff {r : ℕ} (s : Fin r → Fin 6) (v : HexVertex r) :
    hexVertexOpposite v ∈ hexFacet (hexOpposite ∘ s) ↔ v ∈ hexFacet s := by
  simp only [mem_hexFacet, hexVertexOpposite, Function.comp_apply, ← hexOpposite_next]
  rw [hexOpposite_involutive.injective.eq_iff, hexOpposite_involutive.injective.eq_iff]

/-- No simplex contains a vertex together with its antipode. -/
theorem hexVertexOpposite_not_mem_facet {r : ℕ} (s : Fin r → Fin 6) (v : HexVertex r)
    (hv : v ∈ hexFacet s) : hexVertexOpposite v ∉ hexFacet s := by
  have hedge : ∀ a j : Fin 6, (j = a ∨ j = hexNext a) →
      ¬ (hexOpposite j = a ∨ hexOpposite j = hexNext a) := by decide
  exact hedge (s v.1) v.2 ((mem_hexFacet s v).mp hv) ∘ (mem_hexFacet s (hexVertexOpposite v)).mp

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonModTwo` -/


/-!
# The mod-two boundary of the hexagon join

Boundary incidences of the facets pair across adjacent sectors. The pairing
is a fixed-point-free involution preserving the deleted face. Hence the sum
of all facet boundaries is zero over ZMod 2. This is the actual deletion
boundary on finite vertex sets; it is not yet an obstruction to an odd map.
-/

namespace VCDimConvexBound

open scoped BigOperators

abbrev HexBoundaryIncidence (r : ℕ) := (Fin r → Fin 6) × (Fin r × Bool)

/-- Cross the face obtained by deleting one endpoint of an edge. -/
def hexBoundaryMate {r : ℕ} (i : HexBoundaryIncidence r) : HexBoundaryIncidence r :=
  if i.2.2 then
    (Function.update i.1 i.2.1 (hexPrev (i.1 i.2.1)), (i.2.1, false))
  else
    (Function.update i.1 i.2.1 (hexNext (i.1 i.2.1)), (i.2.1, true))

theorem hexBoundaryMate_involutive (r : ℕ) :
    Function.Involutive (@hexBoundaryMate r) := by
  rintro ⟨s, k, b⟩
  cases b <;> simp [hexBoundaryMate, hexPrev_next, hexNext_prev]

theorem hexBoundaryMate_ne_self {r : ℕ} (i : HexBoundaryIncidence r) :
    hexBoundaryMate i ≠ i := by
  rcases i with ⟨s, k, b⟩
  intro h
  have hb := congrArg (fun i : HexBoundaryIncidence r => i.2.2) h
  cases b <;> simp [hexBoundaryMate] at hb

/-- Both incidences in a pair describe exactly the same boundary face. -/
theorem hexRidge_boundaryMate {r : ℕ} (i : HexBoundaryIncidence r) :
    hexRidge (hexBoundaryMate i).1 (hexBoundaryMate i).2 = hexRidge i.1 i.2 := by
  rcases i with ⟨s, k, b⟩
  ext v
  rw [mem_hexRidge, mem_hexRidge]
  by_cases hv : v.1 = k
  · cases b <;> simp [hexBoundaryMate, hv, hexNext_prev]
  · cases b <;> simp [hexBoundaryMate, hv, mem_hexFacet]

/-- Finite mod-two chains, including the empty face for the augmented boundary. -/
abbrev HexModTwoChain (r : ℕ) := Finset (HexVertex r) → ZMod 2

/-- The basis chain of a finite vertex set. -/
def hexFaceBasis {r : ℕ} (t : Finset (HexVertex r)) : HexModTwoChain r :=
  fun f => if t = f then 1 else 0

/-- The usual mod-two simplicial boundary, deleting each vertex once. -/
noncomputable def hexChainBoundary (r : ℕ) : HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain r where
  toFun c := ∑ f : Finset (HexVertex r), c f • ∑ v ∈ f, hexFaceBasis (f.erase v)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [smul_smul, Finset.smul_sum]

theorem hexChainBoundary_basis {r : ℕ} (t : Finset (HexVertex r)) :
    hexChainBoundary r (hexFaceBasis t) = ∑ v ∈ t, hexFaceBasis (t.erase v) := by
  simp [hexChainBoundary, hexFaceBasis]

/-- The boundary formula for the actual 2r-vertex simplex of a sector. -/
theorem hexChainBoundary_facet {r : ℕ} (s : Fin r → Fin 6) :
    hexChainBoundary r (hexFaceBasis (hexFacet s)) =
      ∑ e : Fin r × Bool, hexFaceBasis (hexRidge s e) := by
  rw [hexChainBoundary_basis]
  change (∑ v ∈ Finset.univ.image (hexFacetVertex s),
    hexFaceBasis ((hexFacet s).erase v)) = _
  rw [Finset.sum_image]
  · rfl
  · exact fun a _ b _ h => hexFacetVertex_injective s h

/-- In characteristic two, the two copies of every boundary face cancel. -/
theorem sum_hexRidge_basis_eq_zero (r : ℕ) :
    (∑ i : HexBoundaryIncidence r, hexFaceBasis (hexRidge i.1 i.2)) = 0 := by
  apply Finset.sum_ninvolution hexBoundaryMate
  · intro i
    rw [hexRidge_boundaryMate]
    funext f
    simp only [Pi.add_apply, Pi.zero_apply, hexFaceBasis]
    split_ifs
    · exact (show (1 + 1 : ZMod 2) = 0 from by decide)
    · exact zero_add 0
  · intro i _
    exact hexBoundaryMate_ne_self i
  · intro i
    exact Finset.mem_univ _
  · exact hexBoundaryMate_involutive r

/-- The sum of all sector simplices is a cycle for the deletion boundary. -/
theorem hex_fundamental_boundary_eq_zero (r : ℕ) :
    hexChainBoundary r (∑ s : Fin r → Fin 6, hexFaceBasis (hexFacet s)) = 0 := by
  rw [map_sum]
  simp_rw [hexChainBoundary_facet]
  simpa only [Fintype.sum_prod_type] using sum_hexRidge_basis_eq_zero r

/-- The cycle is a nonzero chain, not cancellation of duplicate facets. -/
theorem hex_fundamental_chain_ne_zero (r : ℕ) :
    (∑ s : Fin r → Fin 6, hexFaceBasis (hexFacet s)) ≠ 0 := by
  intro h
  have he := congrFun h (hexFacet (fun _ : Fin r => (0 : Fin 6)))
  simp [Finset.sum_apply, hexFaceBasis, (hexFacet_injective r).eq_iff] at he

/-- A half of one hexagon has precisely its two antipodal endpoints as boundary. -/
theorem hex_half_cycle_boundary (v : Fin 6) :
    (∑ s ∈ ({0, 1, 2} : Finset (Fin 6)),
      ((if v = s then 1 else 0) + (if v = hexNext s then 1 else 0) : ZMod 2)) =
      (if v = 0 then 1 else 0) + (if v = 3 then 1 else 0) := by
  fin_cases v <;> decide

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonJoinChains` -/


/-!
# Add a color to mod-two chains

A finite set of new hexagon vertices is joined with an old face whose colors
are shifted by one. The two vertex sets are disjoint. The actual deletion
boundary satisfies the mod-two join formula, including empty faces.
-/

namespace VCDimConvexBound

open scoped BigOperators

def hexHeadVertex {r : ℕ} (j : Fin 6) : HexVertex (r + 1) := (0, j)
def hexTailVertex {r : ℕ} (v : HexVertex r) : HexVertex (r + 1) := (v.1.succ, v.2)

theorem hexHeadVertex_injective (r : ℕ) : Function.Injective (@hexHeadVertex r) := by
  intro a b h
  exact congrArg Prod.snd h

theorem hexTailVertex_injective (r : ℕ) : Function.Injective (@hexTailVertex r) := by
  intro a b h
  have h₁ : a.1.succ = b.1.succ := congrArg Prod.fst h
  have h₂ : a.2 = b.2 := congrArg (fun v : HexVertex (r + 1) => v.2) h
  exact Prod.ext (Fin.succ_injective _ h₁) h₂

def hexJoinFace {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    Finset (HexVertex (r + 1)) := a.image hexHeadVertex ∪ t.image hexTailVertex

theorem hexJoinFace_head_mem {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r))
    (j : Fin 6) : hexHeadVertex j ∈ hexJoinFace a t ↔ j ∈ a := by
  simp [hexJoinFace, hexHeadVertex, hexTailVertex]

theorem hexJoinFace_tail_mem {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r))
    (v : HexVertex r) : hexTailVertex v ∈ hexJoinFace a t ↔ v ∈ t := by
  simp [hexJoinFace, hexHeadVertex, hexTailVertex, Prod.mk.injEq, Ne.symm (Fin.succ_ne_zero _)]

theorem hexJoinFace_disjoint {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    Disjoint (a.image (@hexHeadVertex r)) (t.image hexTailVertex) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨w, _, he⟩ := Finset.mem_image.mp hw
  have h := congrArg Prod.fst he
  simp [hexHeadVertex, hexTailVertex] at h

theorem hexJoinFace_erase_head {r : ℕ} (a : Finset (Fin 6))
    (t : Finset (HexVertex r)) (j : Fin 6) :
    (hexJoinFace a t).erase (hexHeadVertex j) = hexJoinFace (a.erase j) t := by
  ext v
  rcases v with ⟨k, l⟩
  refine Fin.cases ?_ (fun k => ?_) k
  · change hexHeadVertex l ∈ _ ↔ hexHeadVertex l ∈ _
    simp only [Finset.mem_erase, hexJoinFace_head_mem]
    simp [hexHeadVertex]
  · change hexTailVertex (k, l) ∈ _ ↔ hexTailVertex (k, l) ∈ _
    simp only [Finset.mem_erase, hexJoinFace_tail_mem]
    simp [hexTailVertex, hexHeadVertex]

theorem hexJoinFace_erase_tail {r : ℕ} (a : Finset (Fin 6))
    (t : Finset (HexVertex r)) (w : HexVertex r) :
    (hexJoinFace a t).erase (hexTailVertex w) = hexJoinFace a (t.erase w) := by
  ext v
  rcases v with ⟨k, l⟩
  refine Fin.cases ?_ (fun k => ?_) k
  · change hexHeadVertex l ∈ _ ↔ hexHeadVertex l ∈ _
    simp only [Finset.mem_erase, hexJoinFace_head_mem]
    simp [hexHeadVertex, hexTailVertex, Ne.symm (Fin.succ_ne_zero _)]
  · change hexTailVertex (k, l) ∈ _ ↔ hexTailVertex (k, l) ∈ _
    simp [Finset.mem_erase, hexJoinFace_tail_mem, (hexTailVertex_injective r).ne_iff]

/-- The join formula on the basis chain of any old face. -/
theorem hexChainBoundary_join_basis {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    hexChainBoundary (r + 1) (hexFaceBasis (hexJoinFace a t)) =
      (∑ j ∈ a, hexFaceBasis (hexJoinFace (a.erase j) t)) +
        ∑ v ∈ t, hexFaceBasis (hexJoinFace a (t.erase v)) := by
  rw [hexChainBoundary_basis]
  change (∑ v ∈ a.image hexHeadVertex ∪ t.image hexTailVertex,
    hexFaceBasis ((hexJoinFace a t).erase v)) = _
  rw [Finset.sum_union (hexJoinFace_disjoint a t)]
  rw [Finset.sum_image (fun i _ j _ h => hexHeadVertex_injective r h),
    Finset.sum_image (fun i _ j _ h => hexTailVertex_injective r h)]
  simp_rw [hexJoinFace_erase_head, hexJoinFace_erase_tail]

/-- Every finite chain is the sum of its basis coefficients. -/
theorem sum_smul_hexFaceBasis {r : ℕ} (c : HexModTwoChain r) :
    (∑ t : Finset (HexVertex r), c t • hexFaceBasis t) = c := by
  funext f
  simp [Finset.sum_apply, Pi.smul_apply, hexFaceBasis, smul_eq_mul]

/-- Equality of linear chain operators can be checked on the face basis. -/
theorem hexChainMap_ext {r p : ℕ}
    (f g : HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain p)
    (h : ∀ t, f (hexFaceBasis t) = g (hexFaceBasis t)) : f = g := by
  apply LinearMap.ext
  intro c
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, h]

/-- Join a fixed new-color face with an arbitrary old chain. -/
noncomputable def hexPrependChain {r : ℕ} (a : Finset (Fin 6)) :
    HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain (r + 1) where
  toFun c := ∑ t : Finset (HexVertex r), c t • hexFaceBasis (hexJoinFace a t)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' x c := by simp [smul_smul, Finset.smul_sum]

theorem hexPrependChain_basis {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    hexPrependChain a (hexFaceBasis t) = hexFaceBasis (hexJoinFace a t) := by
  simp [hexPrependChain, hexFaceBasis]

/-- The mod-two Leibniz rule as an equality of actual boundary operators. -/
theorem hexChainBoundary_prepend_eq {r : ℕ} (a : Finset (Fin 6)) :
    (hexChainBoundary (r + 1)).comp (hexPrependChain a) =
      (∑ j ∈ a, hexPrependChain (a.erase j)) +
        (hexPrependChain a).comp (hexChainBoundary r) := by
  apply hexChainMap_ext
  intro t
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
    hexPrependChain_basis, hexChainBoundary_basis, map_sum]
  simpa only [hexChainBoundary_basis] using hexChainBoundary_join_basis a t

theorem hexChainBoundary_prepend {r : ℕ} (a : Finset (Fin 6)) (c : HexModTwoChain r) :
    hexChainBoundary (r + 1) (hexPrependChain a c) =
      (∑ j ∈ a, hexPrependChain (a.erase j) c) +
        hexPrependChain a (hexChainBoundary r c) := by
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply] using
    congrArg (fun f : HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain (r + 1) => f c)
      (hexChainBoundary_prepend_eq a)

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonHemispheres` -/


/-!
# Hemispheres of the iterated hexagon join

The full cycle in r + 1 colors is the join of the six-edge cycle with the
full cycle in r colors. A three-edge half has boundary equal to the two
antipodal cones. Each cone has boundary equal to the shifted old cycle.
These are chain identities; they do not yet prove an odd-map obstruction.
-/

namespace VCDimConvexBound

open scoped BigOperators

noncomputable def hexFundamentalChain (r : ℕ) : HexModTwoChain r :=
  ∑ s : Fin r → Fin 6, hexFaceBasis (hexFacet s)

theorem hexFundamentalChain_boundary (r : ℕ) :
    hexChainBoundary r (hexFundamentalChain r) = 0 :=
  hex_fundamental_boundary_eq_zero r

theorem hexFundamentalChain_ne_zero (r : ℕ) : hexFundamentalChain r ≠ 0 :=
  hex_fundamental_chain_ne_zero r

theorem hexModTwoChain_add_self {r : ℕ} (c : HexModTwoChain r) : c + c = 0 := by
  funext f
  exact CharTwo.add_self_eq_zero (c f)

/-- Adding the first color is exactly the join of the new edge and the old facet. -/
theorem hexFacet_cons {r : ℕ} (j : Fin 6) (s : Fin r → Fin 6) :
    hexFacet (Fin.cons j s) = hexJoinFace {j, hexNext j} (hexFacet s) := by
  ext v
  rcases v with ⟨k, l⟩
  refine Fin.cases ?_ (fun k => ?_) k
  · change (0, l) ∈ hexFacet (Fin.cons j s) ↔ hexHeadVertex l ∈ _
    rw [hexJoinFace_head_mem]
    simp [mem_hexFacet]
  · change (k.succ, l) ∈ hexFacet (Fin.cons j s) ↔ hexTailVertex (k, l) ∈ _
    rw [hexJoinFace_tail_mem]
    simp [mem_hexFacet]

/-- The six-edge recursion for the full cycle, with no geometric assumption. -/
theorem hexFundamentalChain_succ (r : ℕ) :
    hexFundamentalChain (r + 1) =
      ∑ j : Fin 6, hexPrependChain {j, hexNext j} (hexFundamentalChain r) := by
  unfold hexFundamentalChain
  simp_rw [map_sum, hexPrependChain_basis, ← hexFacet_cons]
  have h := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => Fin 6))
    (fun s => hexFaceBasis (hexFacet s))
  change (∑ x : Fin 6 × (Fin r → Fin 6),
    hexFaceBasis (hexFacet (Fin.cons x.1 x.2))) = _ at h
  simpa only [Fintype.sum_prod_type] using h.symm

/-- A cone over the old fundamental cycle at a vertex of the new hexagon. -/
noncomputable def hexConeChain (r : ℕ) (j : Fin 6) : HexModTwoChain (r + 1) :=
  hexPrependChain {j} (hexFundamentalChain r)

/-- The half using consecutive edges 0--1, 1--2, and 2--3. -/
noncomputable def hexHemisphereChain (r : ℕ) : HexModTwoChain (r + 1) :=
  ∑ j ∈ ({0, 1, 2} : Finset (Fin 6)),
    hexPrependChain {j, hexNext j} (hexFundamentalChain r)

/-- Boundary of a cone is the old cycle embedded in the remaining colors. -/
theorem hexConeChain_boundary (r : ℕ) (j : Fin 6) :
    hexChainBoundary (r + 1) (hexConeChain r j) =
      hexPrependChain ∅ (hexFundamentalChain r) := by
  simp [hexConeChain, hexChainBoundary_prepend, hexFundamentalChain_boundary]

/-- Boundary of the join of a new edge with the old cycle. -/
theorem hexEdgeChain_boundary (r : ℕ) (j : Fin 6) :
    hexChainBoundary (r + 1)
      (hexPrependChain {j, hexNext j} (hexFundamentalChain r)) =
        hexConeChain r j + hexConeChain r (hexNext j) := by
  have hj := hexNext_ne_self j
  have he : ({j, hexNext j} : Finset (Fin 6)).erase (hexNext j) = {j} := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hk₁ | hk₂⟩
      · exact hk₁
      · exact (hk hk₂).elim
    · intro hk
      subst k
      exact ⟨Ne.symm hj, Or.inl rfl⟩
  simp [hexChainBoundary_prepend, hexFundamentalChain_boundary,
    hexConeChain, he, Ne.symm hj, add_comm]

/-- Internal cones cancel: the half has just two antipodal cones as boundary. -/
theorem hexHemisphereChain_boundary (r : ℕ) :
    hexChainBoundary (r + 1) (hexHemisphereChain r) =
      hexConeChain r 0 + hexConeChain r 3 := by
  unfold hexHemisphereChain
  simp_rw [map_sum, hexEdgeChain_boundary]
  have h : (∑ j ∈ ({0, 1, 2} : Finset (Fin 6)),
      (hexConeChain r j + hexConeChain r (hexNext j))) =
      (hexConeChain r 0 + hexConeChain r 1) +
      (hexConeChain r 1 + hexConeChain r 2) +
      (hexConeChain r 2 + hexConeChain r 3) := by
    simp [hexNext, add_assoc]
  rw [h]
  calc
    _ = (hexConeChain r 0 + hexConeChain r 3) +
        (hexConeChain r 1 + hexConeChain r 1) +
        (hexConeChain r 2 + hexConeChain r 2) := by abel
    _ = _ := by simp [hexModTwoChain_add_self]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonAntipodalChains` -/


/-!
# Antipodal symmetry of the hemisphere chains

The antipodal operator changes every color simultaneously. It commutes with
the actual boundary and fixes the full cycle. The full cycle is the sum of a
half and its antipode; the boundary of the half is a cone plus its antipode.
-/

namespace VCDimConvexBound

open scoped BigOperators

theorem hexVertexOpposite_involutive (r : ℕ) :
    Function.Involutive (@hexVertexOpposite r) := by
  intro v
  exact Prod.ext rfl (hexOpposite_involutive v.2)

theorem hexFacet_image_opposite {r : ℕ} (s : Fin r → Fin 6) :
    (hexFacet s).image hexVertexOpposite = hexFacet (hexOpposite ∘ s) := by
  apply Finset.Subset.antisymm
  · rintro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (hexVertexOpposite_mem_facet_iff s w).mpr hw
  · intro v hv
    refine Finset.mem_image.mpr ⟨hexVertexOpposite v, ?_, hexVertexOpposite_involutive r v⟩
    apply (hexVertexOpposite_mem_facet_iff s (hexVertexOpposite v)).mp
    rw [hexVertexOpposite_involutive r v]
    exact hv

theorem hexJoinFace_image_opposite {r : ℕ} (a : Finset (Fin 6))
    (t : Finset (HexVertex r)) :
    (hexJoinFace a t).image hexVertexOpposite =
      hexJoinFace (a.image hexOpposite) (t.image hexVertexOpposite) := by
  simp only [hexJoinFace, Finset.image_union, Finset.image_image]
  rfl

/-- Push a chain through the antipodal involution on all its vertices. -/
noncomputable def hexAntipodalChain (r : ℕ) : HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain r where
  toFun c := ∑ t : Finset (HexVertex r), c t • hexFaceBasis (t.image hexVertexOpposite)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' x c := by simp [smul_smul, Finset.smul_sum]

theorem hexAntipodalChain_basis {r : ℕ} (t : Finset (HexVertex r)) :
    hexAntipodalChain r (hexFaceBasis t) = hexFaceBasis (t.image hexVertexOpposite) := by
  simp [hexAntipodalChain, hexFaceBasis]

theorem hexAntipodalChain_involutive (r : ℕ) :
    Function.Involutive (hexAntipodalChain r) := by
  intro c
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexAntipodalChain_basis, Finset.image_image]
  rw [show (hexVertexOpposite ∘ hexVertexOpposite : HexVertex r → HexVertex r) = id
    from funext (hexVertexOpposite_involutive r)]
  simp only [Finset.image_id]

/-- The global antipodal map is a chain map for the deletion boundary. -/
theorem hexAntipodalChain_boundary {r : ℕ} (c : HexModTwoChain r) :
    hexAntipodalChain r (hexChainBoundary r c) =
      hexChainBoundary r (hexAntipodalChain r c) := by
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexChainBoundary_basis, hexAntipodalChain_basis]
  congr 1
  funext t
  congr 1
  rw [Finset.sum_image]
  · simp_rw [Finset.image_erase (hexVertexOpposite_involutive r).injective]
  · exact fun a _ b _ h => (hexVertexOpposite_involutive r).injective h

/-- The action on a join is antipodal in both the new and old colors. -/
theorem hexAntipodalChain_prepend {r : ℕ} (a : Finset (Fin 6)) (c : HexModTwoChain r) :
    hexAntipodalChain (r + 1) (hexPrependChain a c) =
      hexPrependChain (a.image hexOpposite) (hexAntipodalChain r c) := by
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexPrependChain_basis, hexAntipodalChain_basis,
    hexJoinFace_image_opposite]

/-- All facets together are invariant under the global antipode. -/
theorem hexFundamentalChain_antipodal (r : ℕ) :
    hexAntipodalChain r (hexFundamentalChain r) = hexFundamentalChain r := by
  unfold hexFundamentalChain
  simp_rw [map_sum, hexAntipodalChain_basis, hexFacet_image_opposite]
  let e : (Fin r → Fin 6) ≃ (Fin r → Fin 6) :=
    { toFun := fun s => hexOpposite ∘ s
      invFun := fun s => hexOpposite ∘ s
      left_inv := fun s => funext (fun k => hexOpposite_involutive (s k))
      right_inv := fun s => funext (fun k => hexOpposite_involutive (s k)) }
  exact Equiv.sum_comp e (fun s => hexFaceBasis (hexFacet s))

theorem hexConeChain_antipodal (r : ℕ) (j : Fin 6) :
    hexAntipodalChain (r + 1) (hexConeChain r j) = hexConeChain r (hexOpposite j) := by
  simp [hexConeChain, hexAntipodalChain_prepend, hexFundamentalChain_antipodal]

/-- The half-boundary formula expressed using the genuine global antipode. -/
theorem hexHemisphereChain_boundary_antipodal (r : ℕ) :
    hexChainBoundary (r + 1) (hexHemisphereChain r) =
      hexConeChain r 0 + hexAntipodalChain (r + 1) (hexConeChain r 0) := by
  rw [hexConeChain_antipodal, hexHemisphereChain_boundary]
  rfl

/-- The two antipodal halves sum to the full cycle in every number of colors. -/
theorem hexFundamentalChain_eq_hemisphere_add_antipodal (r : ℕ) :
    hexFundamentalChain (r + 1) = hexHemisphereChain r +
      hexAntipodalChain (r + 1) (hexHemisphereChain r) := by
  rw [hexFundamentalChain_succ]
  unfold hexHemisphereChain
  simp_rw [map_sum, hexAntipodalChain_prepend, hexFundamentalChain_antipodal,
    Finset.image_insert, Finset.image_singleton, hexOpposite_next]
  simp [Fin.sum_univ_succ, hexNext, hexOpposite]
  abel

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonChainSupport` -/


/-!
# Dimensions and face support of hexagon chains

The empty face is allowed here, as required by the augmented boundary.
Positive cardinality will recover membership in the actual simplicial complex.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Every nonzero coefficient is an h-vertex subface of a hexagon facet. -/
def HexChainOnFaces {r : ℕ} (h : ℕ) (c : HexModTwoChain r) : Prop :=
  ∀ t, c t ≠ 0 → t.card = h ∧ ∃ s : Fin r → Fin 6, t ⊆ hexFacet s

theorem hexJoinFace_card {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    (hexJoinFace a t).card = a.card + t.card := by
  rw [hexJoinFace, Finset.card_union_of_disjoint (hexJoinFace_disjoint a t),
    Finset.card_image_of_injective _ (hexHeadVertex_injective r),
    Finset.card_image_of_injective _ (hexTailVertex_injective r)]

theorem hexJoinFace_subset_facet {r : ℕ} {a : Finset (Fin 6)}
    {t : Finset (HexVertex r)} {j : Fin 6} {s : Fin r → Fin 6}
    (ha : a ⊆ {j, hexNext j}) (ht : t ⊆ hexFacet s) :
    hexJoinFace a t ⊆ hexFacet (Fin.cons j s) := by
  rw [hexFacet_cons]
  exact Finset.union_subset_union (Finset.image_subset_image ha) (Finset.image_subset_image ht)

theorem HexChainOnFaces.basis {r h : ℕ} (t : Finset (HexVertex r))
    (ht : t.card = h) (hs : ∃ s : Fin r → Fin 6, t ⊆ hexFacet s) :
    HexChainOnFaces h (hexFaceBasis t) := by
  intro f hf
  have he : t = f := by
    by_contra he
    exact hf (by simp [hexFaceBasis, he])
  subst f
  exact ⟨ht, hs⟩

theorem HexChainOnFaces.sum {r h : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → HexModTwoChain r) (hc : ∀ i ∈ s, HexChainOnFaces h (c i)) :
    HexChainOnFaces h (∑ i ∈ s, c i) := by
  intro t ht
  by_contra hn
  apply ht
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hci
  exact hn (hc i hi t hci)

theorem HexChainOnFaces.prepend {r h : ℕ} {c : HexModTwoChain r}
    (hc : HexChainOnFaces h c) (a : Finset (Fin 6))
    (ha : ∃ j : Fin 6, a ⊆ {j, hexNext j}) :
    HexChainOnFaces (a.card + h) (hexPrependChain a c) := by
  intro f hf
  by_contra hn
  apply hf
  change (∑ t : Finset (HexVertex r), c t • hexFaceBasis (hexJoinFace a t)) f = 0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro t _
  by_cases hct : c t = 0
  · simp [hct]
  by_cases he : hexJoinFace a t = f
  · obtain ⟨ht, s, hs⟩ := hc t hct
    obtain ⟨j, hj⟩ := ha
    exact (hn ⟨he ▸ (hexJoinFace_card a t).trans (congrArg (a.card + ·) ht),
      ⟨Fin.cons j s, he ▸ hexJoinFace_subset_facet hj hs⟩⟩).elim
  · simp [hexFaceBasis, he]

theorem hexFundamentalChain_onFaces (r : ℕ) :
    HexChainOnFaces (2 * r) (hexFundamentalChain r) := by
  apply HexChainOnFaces.sum
  intro s _
  exact HexChainOnFaces.basis _ (card_hexFacet s) ⟨s, Finset.Subset.refl _⟩

theorem hexConeChain_onFaces (r : ℕ) (j : Fin 6) :
    HexChainOnFaces (2 * r + 1) (hexConeChain r j) := by
  have h := (hexFundamentalChain_onFaces r).prepend {j}
    ⟨j, by simp⟩
  simpa [hexConeChain, Nat.add_comm] using h

theorem hexHemisphereChain_onFaces (r : ℕ) :
    HexChainOnFaces (2 * r + 2) (hexHemisphereChain r) := by
  apply HexChainOnFaces.sum
  intro j _
  have h := (hexFundamentalChain_onFaces r).prepend {j, hexNext j}
    ⟨j, Finset.Subset.refl _⟩
  simpa [Finset.card_insert_of_notMem, Ne.symm (hexNext_ne_self j), Nat.add_comm] using h

theorem HexChainOnFaces.mem_faces {r h : ℕ} {c : HexModTwoChain r}
    (hc : HexChainOnFaces h c) (hh : 0 < h) {t : Finset (HexVertex r)} (ht : c t ≠ 0) :
    t ∈ (hexFanComplex r).faces := by
  obtain ⟨hcard, hs⟩ := hc t ht
  exact ⟨Finset.card_pos.mp (hcard ▸ hh), hs⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonHemisphereTower` -/


/-!
# The full graded hemisphere tower

For r colors and 0 ≤ k < 2r, the chain c_k has k+1 vertices per face.
The two new top chains are a half-cycle join and a cone; lower chains are
embedded in the old colors. This gives ∂c_(k+1) = c_k + A c_k in every degree.
-/

namespace VCDimConvexBound

/-- All degrees of the hemisphere construction, in one fixed ambient complex. -/
noncomputable def hexHemisphereTower : (r : ℕ) → ℕ → HexModTwoChain r
  | 0, _ => 0
  | r + 1, k =>
    if k = 2 * r + 1 then hexHemisphereChain r
    else if k = 2 * r then hexConeChain r 0
    else hexPrependChain ∅ (hexHemisphereTower r k)

theorem hexHemisphereTower_top (r : ℕ) :
    hexHemisphereTower (r + 1) (2 * r + 1) = hexHemisphereChain r := by
  simp [hexHemisphereTower]

theorem hexHemisphereTower_cone (r : ℕ) :
    hexHemisphereTower (r + 1) (2 * r) = hexConeChain r 0 := by
  simp [hexHemisphereTower]

theorem hexHemisphereTower_lower {r k : ℕ} (hk : k < 2 * r) :
    hexHemisphereTower (r + 1) k = hexPrependChain ∅ (hexHemisphereTower r k) := by
  rw [hexHemisphereTower, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem hexHemisphereTower_full {r : ℕ} (hr : 0 < r) :
    hexFundamentalChain r = hexHemisphereTower r (2 * r - 1) +
      hexAntipodalChain r (hexHemisphereTower r (2 * r - 1)) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [show 2 * (s + 1) - 1 = 2 * s + 1 by omega, hexHemisphereTower_top]
  exact hexFundamentalChain_eq_hemisphere_add_antipodal s

/-- The actual deletion boundary satisfies the tower recursion in all degrees. -/
theorem hexHemisphereTower_boundary {r k : ℕ} (hk : k + 1 < 2 * r) :
    hexChainBoundary r (hexHemisphereTower r (k + 1)) =
      hexHemisphereTower r k + hexAntipodalChain r (hexHemisphereTower r k) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases htop : k + 1 = 2 * r + 1
    · have he : k = 2 * r := by omega
      subst k
      rw [hexHemisphereTower_top, hexHemisphereTower_cone]
      exact hexHemisphereChain_boundary_antipodal r
    by_cases hcone : k + 1 = 2 * r
    · have hr : 0 < r := by omega
      have he : k = 2 * r - 1 := by omega
      rw [hcone, hexHemisphereTower_cone, hexConeChain_boundary,
        hexHemisphereTower_lower (by omega), he, hexHemisphereTower_full hr,
        map_add, hexAntipodalChain_prepend]
      simp
    · have hlow : k + 1 < 2 * r := by omega
      rw [hexHemisphereTower_lower hlow, hexHemisphereTower_lower (by omega),
        hexChainBoundary_prepend, ih hlow, map_add, hexAntipodalChain_prepend]
      simp

/-- Every tower coefficient is supported on a face of exactly the required degree. -/
theorem hexHemisphereTower_onFaces {r k : ℕ} (hk : k < 2 * r) :
    HexChainOnFaces (k + 1) (hexHemisphereTower r k) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases htop : k = 2 * r + 1
    · subst k
      rw [hexHemisphereTower_top]
      exact hexHemisphereChain_onFaces r
    by_cases hcone : k = 2 * r
    · subst k
      rw [hexHemisphereTower_cone]
      exact hexConeChain_onFaces r 0
    · have hlow : k < 2 * r := by omega
      rw [hexHemisphereTower_lower hlow]
      simpa using (ih hlow).prepend ∅ ⟨0, Finset.empty_subset _⟩

/-- In degree zero the tower consists of one actual vertex, in the last color. -/
theorem hexHemisphereTower_base (r : ℕ) :
    hexHemisphereTower (r + 1) 0 = hexFaceBasis {(Fin.last r, 0)} := by
  induction r with
  | zero =>
    rw [show 0 = 2 * 0 from rfl, hexHemisphereTower_cone]
    simp [hexConeChain, hexFundamentalChain, hexFacet, hexPrependChain_basis,
      hexJoinFace, hexHeadVertex]
  | succ r ih =>
    rw [hexHemisphereTower_lower (by omega), ih, hexPrependChain_basis]
    simp [hexJoinFace, hexTailVertex]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonCochainParity` -/


/-!
# Pairing face cochains with the hemisphere tower

This file proves parity propagation from two explicit identities on actual
faces. It does not assert that geometric crossing indicators satisfy those
identities: transporting the matrix lemmas remains a separate obligation.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Evaluate a face cochain on a finite mod-two chain. -/
noncomputable def hexCochainEval {r : ℕ} (q : HexModTwoChain r) :
    HexModTwoChain r →ₗ[ZMod 2] ZMod 2 where
  toFun c := ∑ f : Finset (HexVertex r), c f * q f
  map_add' c d := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [smul_eq_mul, Finset.mul_sum, mul_assoc]

def hexCoboundary {r : ℕ} (a : HexModTwoChain r) : HexModTwoChain r :=
  fun f => ∑ v ∈ f, a (f.erase v)

def hexAntipodalCochain {r : ℕ} (a : HexModTwoChain r) : HexModTwoChain r :=
  fun f => a (f.image hexVertexOpposite)

theorem hexCochainEval_basis {r : ℕ} (q : HexModTwoChain r) (f : Finset (HexVertex r)) :
    hexCochainEval q (hexFaceBasis f) = q f := by
  simp [hexCochainEval, hexFaceBasis]

theorem hexCochainEval_add {r : ℕ} (q a c : HexModTwoChain r) :
    hexCochainEval (q + a) c = hexCochainEval q c + hexCochainEval a c := by
  simp [hexCochainEval, mul_add, Finset.sum_add_distrib]

/-- Discrete Stokes formula for the actual vertex-deletion boundary. -/
theorem hexCochainEval_coboundary {r : ℕ} (a c : HexModTwoChain r) :
    hexCochainEval (hexCoboundary a) c = hexCochainEval a (hexChainBoundary r c) := by
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexChainBoundary_basis, hexCochainEval_basis, hexCoboundary]

theorem hexCochainEval_antipodal {r : ℕ} (a c : HexModTwoChain r) :
    hexCochainEval (hexAntipodalCochain a) c =
      hexCochainEval a (hexAntipodalChain r c) := by
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexAntipodalChain_basis, hexCochainEval_basis,
    hexAntipodalCochain]

/-- Cochain equality is needed only on the dimension and complex supporting c. -/
theorem hexCochainEval_congr_onFaces {r h : ℕ} {c : HexModTwoChain r}
    (hc : HexChainOnFaces h c) (hh : 0 < h) (q a : HexModTwoChain r)
    (he : ∀ f ∈ (hexFanComplex r).faces, f.card = h → q f = a f) :
    hexCochainEval q c = hexCochainEval a c := by
  change (∑ f, c f * q f) = ∑ f, c f * a f
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : c f = 0
  · simp [hf]
  · rw [he f (hc.mem_faces hh hf) (hc f hf).1]

/-- A nonzero evaluation has a face contributing to it. -/
theorem hexCochainEval_exists {r : ℕ} {q c : HexModTwoChain r}
    (h : hexCochainEval q c ≠ 0) :
    ∃ f, c f ≠ 0 ∧ q f ≠ 0 := by
  obtain ⟨f, _, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨f, left_ne_zero_of_mul hf, right_ne_zero_of_mul hf⟩

/-- One step of parity propagation, assuming the two identities on actual faces. -/
theorem hexHemisphereTower_parity_step {r k : ℕ} (hk : k + 1 < 2 * r)
    (qNext q a : HexModTwoChain r)
    (hboundary : ∀ f ∈ (hexFanComplex r).faces, f.card = k + 2 →
      qNext f = hexCoboundary a f)
    (hantipodal : ∀ f ∈ (hexFanComplex r).faces, f.card = k + 1 →
      q f = a f + hexAntipodalCochain a f) :
    hexCochainEval qNext (hexHemisphereTower r (k + 1)) =
      hexCochainEval q (hexHemisphereTower r k) := by
  calc
    _ = hexCochainEval (hexCoboundary a) (hexHemisphereTower r (k + 1)) :=
      hexCochainEval_congr_onFaces (hexHemisphereTower_onFaces hk) (by omega)
        _ _ hboundary
    _ = hexCochainEval a (hexChainBoundary r (hexHemisphereTower r (k + 1))) :=
      hexCochainEval_coboundary _ _
    _ = hexCochainEval a (hexHemisphereTower r k) +
        hexCochainEval a (hexAntipodalChain r (hexHemisphereTower r k)) := by
      rw [hexHemisphereTower_boundary hk, map_add]
    _ = hexCochainEval (a + hexAntipodalCochain a) (hexHemisphereTower r k) := by
      rw [hexCochainEval_add, hexCochainEval_antipodal]
    _ = hexCochainEval q (hexHemisphereTower r k) :=
      (hexCochainEval_congr_onFaces (hexHemisphereTower_onFaces (by omega))
        (by omega) _ _ hantipodal).symm

/-- All tower evaluations are one, conditional on the face-level flag identities. -/
theorem hexHemisphereTower_parity_one {r : ℕ}
    (q a : ℕ → HexModTwoChain r)
    (hbase : ∀ v : HexVertex r, q 0 {v} = 1)
    (hboundary : ∀ k, k + 1 < 2 * r →
      ∀ f ∈ (hexFanComplex r).faces, f.card = k + 2 →
        q (k + 1) f = hexCoboundary (a k) f)
    (hantipodal : ∀ k, k + 1 < 2 * r →
      ∀ f ∈ (hexFanComplex r).faces, f.card = k + 1 →
        q k f = a k f + hexAntipodalCochain (a k) f)
    {k : ℕ} (hk : k < 2 * r) :
    hexCochainEval (q k) (hexHemisphereTower r k) = 1 := by
  induction k with
  | zero =>
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    rw [hexHemisphereTower_base, hexCochainEval_basis]
    exact hbase _
  | succ k ih =>
    rw [hexHemisphereTower_parity_step hk (q (k + 1)) (q k) (a k)
      (hboundary k hk) (hantipodal k hk)]
    exact ih (by omega)

/-- The face-level identities force a top-dimensional facet with nonzero q. -/
theorem hexHemisphereTower_exists_top_crossing {r : ℕ} (hr : 0 < r)
    (q a : ℕ → HexModTwoChain r)
    (hbase : ∀ v : HexVertex r, q 0 {v} = 1)
    (hboundary : ∀ k, k + 1 < 2 * r →
      ∀ f ∈ (hexFanComplex r).faces, f.card = k + 2 →
        q (k + 1) f = hexCoboundary (a k) f)
    (hantipodal : ∀ k, k + 1 < 2 * r →
      ∀ f ∈ (hexFanComplex r).faces, f.card = k + 1 →
        q k f = a k f + hexAntipodalCochain (a k) f) :
    ∃ s : Fin r → Fin 6, q (2 * r - 1) (hexFacet s) ≠ 0 := by
  have hk : 2 * r - 1 < 2 * r := by omega
  have h := hexHemisphereTower_parity_one q a hbase hboundary hantipodal hk
  obtain ⟨f, hf, hq⟩ := hexCochainEval_exists (show
    hexCochainEval (q (2 * r - 1)) (hexHemisphereTower r (2 * r - 1)) ≠ 0 by
      rw [h]; exact one_ne_zero)
  obtain ⟨hcard, s, hs⟩ := hexHemisphereTower_onFaces hk f hf
  have he : f = hexFacet s := Finset.eq_of_subset_of_card_le hs (by
    rw [card_hexFacet, hcard]; omega)
  exact ⟨s, he ▸ hq⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.AffineSliceInterval` -/


/-!
# The nonnegative part of an affine line

This is the one-dimensional inequality step for the coordinate-flag route.
It does not construct the affine line from the coordinate equations or prove
that the required general-position conditions hold for vertex images.
-/

namespace VCDimConvexBound

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The coefficient vector on a parameterized affine line. -/
def sliceCoeff (a w : ι → ℝ) (t : ℝ) (i : ι) : ℝ := a i + t * w i

/-- Parameters whose coefficient vector is in the nonnegative orthant. -/
def sliceFeasible (a w : ι → ℝ) (t : ℝ) : Prop := ∀ i, 0 ≤ sliceCoeff a w t i

/-- No two distinct coordinates vanish at the same parameter. Later this
condition must be deduced from the augmented general-position minors. -/
def sliceNoDoubleZero (a w : ι → ℝ) : Prop :=
  ∀ i j t, sliceCoeff a w t i = 0 → sliceCoeff a w t j = 0 → i = j

theorem sliceCoeff_nonneg_of_pos {a w t : ℝ} (hw : 0 < w) :
    0 ≤ a + t * w ↔ -a / w ≤ t := by
  rw [div_le_iff₀ hw]
  constructor <;> intro h <;> linarith

theorem sliceCoeff_nonneg_of_neg {a w t : ℝ} (hw : w < 0) :
    0 ≤ a + t * w ↔ t ≤ -a / w := by
  rw [le_div_iff_of_neg hw]
  constructor <;> intro h <;> linarith

theorem sliceCoeff_at_root (a w : ℝ) (hw : w ≠ 0) :
    a + (-a / w) * w = 0 := by
  rw [div_mul_cancel₀ _ hw]
  exact add_neg_cancel a

/-- A nonzero direction tangent to the mass-one hyperplane has both signs. -/
theorem sliceDirection_has_both_signs (w : ι → ℝ) (hsum : ∑ i, w i = 0)
    (hne : w ≠ 0) : (∃ i, 0 < w i) ∧ (∃ i, w i < 0) := by
  have hex : ∃ i ∈ Finset.univ, w i ≠ 0 := by
    by_contra! h
    apply hne
    funext i
    exact h i (Finset.mem_univ i)
  obtain ⟨p, _, hp⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero w hsum hex
  have hneg : ∑ i, -w i = 0 := by rw [Finset.sum_neg_distrib, hsum, neg_zero]
  have hexneg : ∃ i ∈ Finset.univ, -w i ≠ 0 := by
    obtain ⟨i, hi, hwi⟩ := hex
    exact ⟨i, hi, neg_ne_zero.mpr hwi⟩
  obtain ⟨n, _, hn⟩ :=
    Finset.exists_pos_of_sum_zero_of_exists_nonzero (fun i => -w i) hneg hexneg
  exact ⟨⟨p, hp⟩, ⟨n, by linarith⟩⟩

/-- Choose the active lower and upper constraints. The endpoints are the
maximum positive-slope root and the minimum negative-slope root. This also
covers an empty feasible set, when the lower root exceeds the upper root. -/
theorem exists_slice_interval (a w : ι → ℝ)
    (hpos : ∃ i, 0 < w i) (hneg : ∃ i, w i < 0)
    (hzero : ∀ i, w i = 0 → 0 ≤ a i) :
    ∃ p n : ι, 0 < w p ∧ w n < 0 ∧
      (∀ i, 0 < w i → -a i / w i ≤ -a p / w p) ∧
      (∀ i, w i < 0 → -a n / w n ≤ -a i / w i) ∧
      (∀ t, sliceFeasible a w t ↔ -a p / w p ≤ t ∧ t ≤ -a n / w n) := by
  classical
  let P := Finset.univ.filter fun i => 0 < w i
  let N := Finset.univ.filter fun i => w i < 0
  have hP : P.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hN : N.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨p, hp, hpmax⟩ := P.exists_max_image (fun i => -a i / w i) hP
  obtain ⟨n, hn, hnmin⟩ := N.exists_min_image (fun i => -a i / w i) hN
  have hwp : 0 < w p := (Finset.mem_filter.mp hp).2
  have hwn : w n < 0 := (Finset.mem_filter.mp hn).2
  have hpmax' : ∀ i, 0 < w i → -a i / w i ≤ -a p / w p := by
    intro i hi
    exact hpmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hnmin' : ∀ i, w i < 0 → -a n / w n ≤ -a i / w i := by
    intro i hi
    exact hnmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  refine ⟨p, n, hwp, hwn, hpmax', hnmin', ?_⟩
  intro t
  constructor
  · intro ht
    exact ⟨(sliceCoeff_nonneg_of_pos hwp).mp (ht p),
      (sliceCoeff_nonneg_of_neg hwn).mp (ht n)⟩
  · rintro ⟨hL, hU⟩ i
    rcases lt_trichotomy (w i) 0 with hi | hi | hi
    · exact (sliceCoeff_nonneg_of_neg hi).mpr (hU.trans (hnmin' i hi))
    · simpa [sliceCoeff, hi] using hzero i hi
    · exact (sliceCoeff_nonneg_of_pos hi).mpr ((hpmax' i hi).trans hL)

/-- The closed-interval formulation, including the active endpoint coordinates. -/
theorem exists_slice_interval_endpoints (a w : ι → ℝ)
    (hsum : ∑ i, w i = 0) (hne : w ≠ 0)
    (hzero : ∀ i, w i = 0 → 0 ≤ a i) :
    ∃ L U : ℝ, (∀ t, sliceFeasible a w t ↔ L ≤ t ∧ t ≤ U) ∧
      (∃ p, 0 < w p ∧ sliceCoeff a w L p = 0) ∧
      (∃ n, w n < 0 ∧ sliceCoeff a w U n = 0) := by
  obtain ⟨hpos, hneg⟩ := sliceDirection_has_both_signs w hsum hne
  obtain ⟨p, n, hp, hn, _, _, hI⟩ := exists_slice_interval a w hpos hneg hzero
  exact ⟨-a p / w p, -a n / w n, hI,
    ⟨p, hp, sliceCoeff_at_root (a p) (w p) (ne_of_gt hp)⟩,
    ⟨n, hn, sliceCoeff_at_root (a n) (w n) (ne_of_lt hn)⟩⟩

/-- Along a mass-preserving direction the coefficient sum is constant. -/
theorem sum_sliceCoeff (a w : ι → ℝ) (t : ℝ) (hw : ∑ i, w i = 0) :
    ∑ i, sliceCoeff a w t i = ∑ i, a i := by
  simp [sliceCoeff, Finset.sum_add_distrib, ← Finset.mul_sum, hw]

omit [Fintype ι] in
/-- With nonzero slope, a nonnegative affine function at both endpoints
is strictly positive at every interior parameter. -/
theorem sliceCoeff_pos_between (a w : ι → ℝ) {L U t : ℝ}
    (hL : sliceFeasible a w L) (hU : sliceFeasible a w U)
    (hLt : L < t) (htU : t < U) (hw : ∀ i, w i ≠ 0) :
    ∀ i, 0 < sliceCoeff a w t i := by
  intro i
  have hLi := hL i
  have hUi := hU i
  unfold sliceCoeff at *
  rcases lt_or_gt_of_ne (hw i) with hi | hi
  · have hmul := mul_pos (sub_pos.mpr htU) (neg_pos.mpr hi)
    nlinarith
  · have hmul := mul_pos (sub_pos.mpr hLt) hi
    nlinarith

/-- Under explicit genericity assumptions, every nonempty feasible interval
has two distinct endpoints, exactly one zero coordinate at each endpoint,
and strictly positive coordinates at every interior parameter. -/
theorem exists_generic_slice_endpoints (a w : ι → ℝ)
    (hsum : ∑ i, w i = 0) (hne : w ≠ 0)
    (hw : ∀ i, w i ≠ 0) (hG : sliceNoDoubleZero a w)
    (hfeas : ∃ t, sliceFeasible a w t) :
    ∃ L U : ℝ, ∃ p n : ι,
      L < U ∧ p ≠ n ∧ 0 < w p ∧ w n < 0 ∧
      (∀ t, sliceFeasible a w t ↔ L ≤ t ∧ t ≤ U) ∧
      (∀ i, sliceCoeff a w L i = 0 ↔ i = p) ∧
      (∀ i, sliceCoeff a w U i = 0 ↔ i = n) ∧
      (∀ t, L < t → t < U → ∀ i, 0 < sliceCoeff a w t i) ∧
      (∀ t, (sliceFeasible a w t ∧ ∃ i, sliceCoeff a w t i = 0) ↔
        t = L ∨ t = U) := by
  obtain ⟨L, U, hI, ⟨p, hp, hLp⟩, ⟨n, hn, hUn⟩⟩ :=
    exists_slice_interval_endpoints a w hsum hne (fun i hi => (hw i hi).elim)
  have hpn : p ≠ n := by rintro rfl; linarith
  have hLU : L < U := by
    obtain ⟨t, ht⟩ := hfeas
    have hle : L ≤ U := (hI t |>.mp ht).1.trans (hI t |>.mp ht).2
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact hpn (hG p n L hLp (heq.symm ▸ hUn))
  have hL : sliceFeasible a w L := (hI L).mpr ⟨le_rfl, hLU.le⟩
  have hU : sliceFeasible a w U := (hI U).mpr ⟨hLU.le, le_rfl⟩
  have hpos : ∀ t, L < t → t < U → ∀ i, 0 < sliceCoeff a w t i := by
    intro t htL htU
    exact sliceCoeff_pos_between a w hL hU htL htU hw
  refine ⟨L, U, p, n, hLU, hpn, hp, hn, hI, ?_, ?_, hpos, ?_⟩
  · intro i
    exact ⟨fun hi => hG i p L hi hLp, fun hi => hi ▸ hLp⟩
  · intro i
    exact ⟨fun hi => hG i n U hi hUn, fun hi => hi ▸ hUn⟩
  · intro t
    constructor
    · rintro ⟨ht, i, hi⟩
      obtain ⟨htL, htU⟩ := (hI t).mp ht
      by_contra! h
      have hposi := hpos t (lt_of_le_of_ne htL (Ne.symm h.1))
        (lt_of_le_of_ne htU h.2) i
      linarith
    · rintro (rfl | rfl)
      · exact ⟨hL, p, hLp⟩
      · exact ⟨hU, n, hUn⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SliceConstraintMatrix` -/


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


/-! ## Source module `VCDimConvexBound.AffineIntervalParity` -/


/-!
# Scalar crossing parity on a closed interval

An affine scalar function with nonzero endpoint values has an interior zero
exactly when its endpoint signs differ. Its positive endpoint count modulo
two therefore detects that zero. This is the scalar ingredient, not yet the
cochain identity on the faces of a simplex.
-/

namespace VCDimConvexBound

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- A nonconstant affine scalar function has at most one zero. -/
theorem affineScalar_zero_unique {c d s t : ℝ} (hd : d ≠ 0)
    (hs : c + s * d = 0) (ht : c + t * d = 0) : s = t := by
  apply mul_right_cancel₀ hd
  linarith

/-- An interior zero is equivalent to opposite strict endpoint signs. -/
theorem affineScalar_crossing_iff {c d L U : ℝ} (hd : d ≠ 0) (hLU : L < U) :
    (∃ t, L < t ∧ t < U ∧ c + t * d = 0) ↔
      (c + L * d < 0 ∧ 0 < c + U * d) ∨
      (0 < c + L * d ∧ c + U * d < 0) := by
  rcases lt_or_gt_of_ne hd with hd | hd
  · constructor
    · rintro ⟨t, htL, htU, ht⟩
      have h₁ := mul_pos (sub_pos.mpr htL) (neg_pos.mpr hd)
      have h₂ := mul_pos (sub_pos.mpr htU) (neg_pos.mpr hd)
      right
      constructor <;> nlinarith
    · intro h
      have hdec := mul_pos (sub_pos.mpr hLU) (neg_pos.mpr hd)
      have hsign : 0 < c + L * d ∧ c + U * d < 0 := by
        rcases h with h | h
        · exfalso; nlinarith [h.1, h.2]
        · exact h
      refine ⟨-c / d, ?_, ?_, sliceCoeff_at_root c d (ne_of_lt hd)⟩
      · rw [lt_div_iff_of_neg hd]
        linarith [hsign.1]
      · rw [div_lt_iff_of_neg hd]
        linarith [hsign.2]
  · constructor
    · rintro ⟨t, htL, htU, ht⟩
      have h₁ := mul_pos (sub_pos.mpr htL) hd
      have h₂ := mul_pos (sub_pos.mpr htU) hd
      left
      constructor <;> nlinarith
    · intro h
      have hinc := mul_pos (sub_pos.mpr hLU) hd
      have hsign : c + L * d < 0 ∧ 0 < c + U * d := by
        rcases h with h | h
        · exact h
        · exfalso; nlinarith [h.1, h.2]
      refine ⟨-c / d, ?_, ?_, sliceCoeff_at_root c d (ne_of_gt hd)⟩
      · rw [lt_div_iff₀ hd]
        linarith [hsign.1]
      · rw [div_lt_iff₀ hd]
        linarith [hsign.2]

/-- The crossing detected by the signs is a unique interior zero. -/
theorem affineScalar_unique_crossing_iff {c d L U : ℝ} (hd : d ≠ 0) (hLU : L < U) :
    (∃! t, L < t ∧ t < U ∧ c + t * d = 0) ↔
      (c + L * d < 0 ∧ 0 < c + U * d) ∨
      (0 < c + L * d ∧ c + U * d < 0) := by
  constructor
  · intro h
    exact (affineScalar_crossing_iff hd hLU).mp h.exists
  · intro h
    obtain ⟨t, ht⟩ := (affineScalar_crossing_iff hd hLU).mpr h
    exact ⟨t, ht, fun s hs => affineScalar_zero_unique hd hs.2.2 ht.2.2⟩

/-- The mod-two indicator of a strictly positive real value. -/
noncomputable def positiveBit (x : ℝ) : ZMod 2 := if 0 < x then 1 else 0

/-- Two nonzero values contribute an odd count exactly when their signs differ. -/
theorem positiveBit_add (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    positiveBit x + positiveBit y =
      if (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0) then 1 else 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;>
    rcases lt_or_gt_of_ne hy with hy | hy <;>
    simp [positiveBit, hx, hy, not_lt.mpr (le_of_lt hx),
      not_lt.mpr (le_of_lt hy), CharTwo.add_self_eq_zero]

/-- Positive endpoint count modulo two equals the indicator of an interior zero. -/
theorem affineScalar_endpoint_parity {c d L U : ℝ} (hd : d ≠ 0) (hLU : L < U)
    (hL : c + L * d ≠ 0) (hU : c + U * d ≠ 0) :
    positiveBit (c + L * d) + positiveBit (c + U * d) =
      if ∃ t, L < t ∧ t < U ∧ c + t * d = 0 then 1 else 0 := by
  simp only [positiveBit_add _ _ hL hU, affineScalar_crossing_iff hd hLU]

/-- Evaluate a scalar vertex coordinate on an affine coefficient line. -/
def sliceHeight {ι : Type*} [Fintype ι] (a w z : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, sliceCoeff a w t i * z i

theorem sliceHeight_eq_affine {ι : Type*} [Fintype ι] (a w z : ι → ℝ) (t : ℝ) :
    sliceHeight a w z t = (∑ i, a i * z i) + t * ∑ i, w i * z i := by
  simp only [sliceHeight, sliceCoeff, add_mul, Finset.sum_add_distrib,
    mul_assoc, Finset.mul_sum]

/-- Apply scalar parity to a height coordinate of a nonnegative coefficient
slice. Endpoint nonvanishing makes feasible zeros exactly interior zeros. -/
theorem sliceHeight_endpoint_parity {ι : Type*} [Fintype ι]
    (a w z : ι → ℝ) {L U : ℝ} (hLU : L < U)
    (hI : ∀ t, sliceFeasible a w t ↔ L ≤ t ∧ t ≤ U)
    (hd : ∑ i, w i * z i ≠ 0)
    (hL : sliceHeight a w z L ≠ 0) (hU : sliceHeight a w z U ≠ 0) :
    positiveBit (sliceHeight a w z L) + positiveBit (sliceHeight a w z U) =
      if ∃ t, sliceFeasible a w t ∧ sliceHeight a w z t = 0 then 1 else 0 := by
  have hex : (∃ t, L < t ∧ t < U ∧ sliceHeight a w z t = 0) ↔
      (∃ t, sliceFeasible a w t ∧ sliceHeight a w z t = 0) := by
    constructor
    · rintro ⟨t, htL, htU, ht⟩
      exact ⟨t, (hI t).mpr ⟨htL.le, htU.le⟩, ht⟩
    · rintro ⟨t, ht, hz⟩
      obtain ⟨htL, htU⟩ := (hI t).mp ht
      have hneL : L ≠ t := by rintro rfl; exact hL hz
      have hneU : t ≠ U := by rintro rfl; exact hU hz
      exact ⟨t, lt_of_le_of_ne htL hneL, lt_of_le_of_ne htU hneU, hz⟩
  simp_rw [sliceHeight_eq_affine] at hL hU hex ⊢
  rw [affineScalar_endpoint_parity hd hLU hL hU, hex]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.FlagSliceMatrix` -/


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


/-! ## Source module `VCDimConvexBound.FlagSliceInterval` -/


/-!
# From coordinate matrices to the two-endpoint parity identity

The affine-line and nondegeneracy hypotheses are now derived from explicit
minor conditions on the original coordinate constraints. The remaining
local cochain step is to identify the two endpoint terms with the sum over
all abstract boundary faces. General-position perturbation is also pending.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

/-- A nonnegative mass-one solution of the coordinate equations. -/
def flagSlicePoint {r : ℕ} (X : Matrix (Fin r) (Fin (r + 2)) ℝ)
    (x : Fin (r + 2) → ℝ) : Prop :=
  (∑ i, x i) = 1 ∧ X *ᵥ x = 0 ∧ ∀ i, 0 ≤ x i

/-- The full interval description for an actual nonempty coordinate slice.
All genericity hypotheses of the earlier scalar lemmas follow from minors. -/
theorem exists_flagSlice_interval {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hG : FlagSliceGeneric X z) (hfeas : ∃ x, flagSlicePoint X x) :
    ∃ a w : Fin (r + 2) → ℝ, ∃ L U : ℝ, ∃ p n : Fin (r + 2),
      L < U ∧ p ≠ n ∧
      (∀ x, ((∑ i, x i) = 1 ∧ X *ᵥ x = 0) ↔ ∃ t : ℝ, x = sliceCoeff a w t) ∧
      (∀ t, sliceFeasible a w t ↔ L ≤ t ∧ t ≤ U) ∧
      (∀ i, sliceCoeff a w L i = 0 ↔ i = p) ∧
      (∀ i, sliceCoeff a w U i = 0 ↔ i = n) ∧
      (∀ t, L < t → t < U → ∀ i, 0 < sliceCoeff a w t i) ∧
      (∀ t, (sliceFeasible a w t ∧ ∃ i, sliceCoeff a w t i = 0) ↔ t = L ∨ t = U) ∧
      (∑ i, w i * z i) ≠ 0 ∧
      sliceHeight a w z L ≠ 0 ∧ sliceHeight a w z U ≠ 0 := by
  obtain ⟨a, w, _, _, hw, _, hne, hwi, hNo, hz, hline⟩ := exists_flagSlice_line X z hG
  have htfeas : ∃ t, sliceFeasible a w t := by
    obtain ⟨x, hmass, hX, hnonneg⟩ := hfeas
    obtain ⟨t, rfl⟩ := (hline x).mp ⟨hmass, hX⟩
    exact ⟨t, hnonneg⟩
  obtain ⟨L, U, p, n, hLU, hpn, _, _, hI, hLp, hUn, hint, hboundary⟩ :=
    exists_generic_slice_endpoints a w hw hne hwi hNo htfeas
  refine ⟨a, w, L, U, p, n, hLU, hpn, hline, hI, hLp, hUn, hint, hboundary, hz, ?_, ?_⟩
  · have ht := (hline (sliceCoeff a w L)).mpr ⟨L, rfl⟩
    exact flagSlice_boundary_height_ne_zero X z hG.height_minors _ ht.1 ht.2 p
      ((hLp p).mpr rfl)
  · have ht := (hline (sliceCoeff a w U)).mpr ⟨U, rfl⟩
    exact flagSlice_boundary_height_ne_zero X z hG.height_minors _ ht.1 ht.2 n
      ((hUn n).mpr rfl)

/-- The actual coordinate slice has two distinct boundary points, each with
one zero coefficient, whose positive-height count detects a height-zero
solution modulo two. The boundary-face indexing step is not asserted here. -/
theorem exists_flagSlice_endpoint_parity {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hG : FlagSliceGeneric X z) (hfeas : ∃ x, flagSlicePoint X x) :
    ∃ l u : Fin (r + 2) → ℝ, ∃ p n : Fin (r + 2),
      flagSlicePoint X l ∧ flagSlicePoint X u ∧ l ≠ u ∧ p ≠ n ∧
      (∀ i, l i = 0 ↔ i = p) ∧ (∀ i, u i = 0 ↔ i = n) ∧
      positiveBit (∑ i, l i * z i) + positiveBit (∑ i, u i * z i) =
        if ∃ x, flagSlicePoint X x ∧ (∑ i, x i * z i) = 0 then 1 else 0 := by
  obtain ⟨a, w, L, U, p, n, hLU, hpn, hline, hI, hLp, hUn, _, _, hd, hL, hU⟩ :=
    exists_flagSlice_interval X z hG hfeas
  have hLl := (hline (sliceCoeff a w L)).mpr ⟨L, rfl⟩
  have hUl := (hline (sliceCoeff a w U)).mpr ⟨U, rfl⟩
  have hl : flagSlicePoint X (sliceCoeff a w L) :=
    ⟨hLl.1, hLl.2, (hI L).mpr ⟨le_rfl, hLU.le⟩⟩
  have hu : flagSlicePoint X (sliceCoeff a w U) :=
    ⟨hUl.1, hUl.2, (hI U).mpr ⟨hLU.le, le_rfl⟩⟩
  have hne : sliceCoeff a w L ≠ sliceCoeff a w U := by
    intro heq
    have hzL := (hLp p).mpr rfl
    rw [heq] at hzL
    exact hpn ((hUn p).mp hzL)
  refine ⟨sliceCoeff a w L, sliceCoeff a w U, p, n, hl, hu, hne, hpn, hLp, hUn, ?_⟩
  have hex : (∃ t, sliceFeasible a w t ∧ sliceHeight a w z t = 0) ↔
      (∃ x, flagSlicePoint X x ∧ (∑ i, x i * z i) = 0) := by
    constructor
    · rintro ⟨t, ht, hz⟩
      have heq := (hline (sliceCoeff a w t)).mpr ⟨t, rfl⟩
      exact ⟨sliceCoeff a w t, ⟨heq.1, heq.2, ht⟩, hz⟩
    · rintro ⟨x, hx, hz⟩
      obtain ⟨t, rfl⟩ := (hline x).mp ⟨hx.1, hx.2.1⟩
      exact ⟨t, hx.2.2, hz⟩
  change positiveBit (sliceHeight a w z L) + positiveBit (sliceHeight a w z U) = _
  rw [sliceHeight_endpoint_parity a w z hLU hI hd hL hU, hex]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.FlagFaceCrossings` -/


/-!
# Crossing indicators and actual deleted-column faces

Crossings use barycentric coefficients on a finite vertex set. Deleting a
vertex means restricting the coordinate and height rows to the remaining
columns. Inserting a zero coefficient identifies these crossings with the
corresponding boundary of the full coefficient simplex.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

/-- A barycentric solution of an arbitrary finite-column coordinate system. -/
def flagCrossingPoint {ρ ι : Type*} [Fintype ι] (X : Matrix ρ ι ℝ) (x : ι → ℝ) : Prop :=
  (∑ i, x i) = 1 ∧ X *ᵥ x = 0 ∧ ∀ i, 0 ≤ x i

/-- The indicator that the coordinate plane meets the coefficient simplex. -/
noncomputable def flagZeroBit {ρ ι : Type*} [Fintype ι] (X : Matrix ρ ι ℝ) : ZMod 2 :=
  if ∃ x, flagCrossingPoint X x then 1 else 0

/-- A crossing whose next coordinate is strictly positive. -/
def flagHasPositiveCrossing {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) : Prop :=
  ∃ x, flagCrossingPoint X x ∧ 0 < ∑ i, x i * z i

noncomputable def flagPositiveBit {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) : ZMod 2 :=
  if flagHasPositiveCrossing X z then 1 else 0

/-- A positive crossing on the boundary where the coefficient of p is zero. -/
def flagHasBoundaryCrossing {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) (p : ι) : Prop :=
  ∃ x, flagCrossingPoint X x ∧ x p = 0 ∧ 0 < ∑ i, x i * z i

/-- Inserting a zero coefficient preserves total mass. -/
theorem sum_insertNth_zero {k : ℕ} (p : Fin (k + 1)) (x : Fin k → ℝ) :
    ∑ i, Fin.insertNth p 0 x i = ∑ j, x j := by
  rw [Fin.sum_univ_succAbove _ p]
  simp

/-- Inserting a zero coefficient preserves every weighted scalar coordinate. -/
theorem sum_insertNth_zero_mul {k : ℕ} (p : Fin (k + 1))
    (x : Fin k → ℝ) (z : Fin (k + 1) → ℝ) :
    ∑ i, (Fin.insertNth p 0 x : Fin (k + 1) → ℝ) i * z i = ∑ j, x j * z (p.succAbove j) := by
  rw [Fin.sum_univ_succAbove _ p]
  simp

/-- A zero coefficient can be removed and then restored exactly. -/
theorem insertNth_zero_restrict {k : ℕ} (p : Fin (k + 1))
    (x : Fin (k + 1) → ℝ) (hp : x p = 0) :
    Fin.insertNth p 0 (fun j => x (p.succAbove j)) = x := by
  funext i
  refine Fin.succAboveCases p ?_ (fun j => ?_) i
  · simpa using hp.symm
  · simp

/-- The inserted coefficient vector has the same image under the coordinate matrix. -/
theorem mulVec_insertNth_zero {ρ : Type*} {k : ℕ}
    (X : Matrix ρ (Fin (k + 1)) ℝ) (p : Fin (k + 1)) (x : Fin k → ℝ) :
    X *ᵥ Fin.insertNth p 0 x = X.submatrix id p.succAbove *ᵥ x := by
  have h := mulVec_delete_zero X (Fin.insertNth p 0 x) p (by simp)
  simpa using h.symm

/-- Face feasibility is exactly full-simplex feasibility after zero insertion. -/
theorem flagCrossingPoint_insert_zero_iff {ρ : Type*} {k : ℕ}
    (X : Matrix ρ (Fin (k + 1)) ℝ) (p : Fin (k + 1)) (x : Fin k → ℝ) :
    flagCrossingPoint X (Fin.insertNth p 0 x) ↔
      flagCrossingPoint (X.submatrix id p.succAbove) x := by
  unfold flagCrossingPoint
  rw [sum_insertNth_zero, mulVec_insertNth_zero]
  constructor
  · rintro ⟨hm, hX, hnonneg⟩
    exact ⟨hm, hX, fun j => by simpa using hnonneg (p.succAbove j)⟩
  · rintro ⟨hm, hX, hnonneg⟩
    refine ⟨hm, hX, ?_⟩
    intro i
    refine Fin.succAboveCases p ?_ (fun j => ?_) i
    · simp
    · simpa using hnonneg j

/-- A positive crossing on a deleted-column face is precisely a boundary crossing. -/
theorem flagPositiveCrossing_face_iff {ρ : Type*} {k : ℕ}
    (X : Matrix ρ (Fin (k + 1)) ℝ) (z : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    flagHasPositiveCrossing (X.submatrix id p.succAbove) (fun j => z (p.succAbove j)) ↔
      flagHasBoundaryCrossing X z p := by
  constructor
  · rintro ⟨x, hx, hz⟩
    exact ⟨Fin.insertNth p 0 x, (flagCrossingPoint_insert_zero_iff X p x).mpr hx,
      by simp, by simpa only [sum_insertNth_zero_mul] using hz⟩
  · rintro ⟨x, hx, hp, hz⟩
    let y := fun j => x (p.succAbove j)
    have heq : Fin.insertNth p 0 y = x := insertNth_zero_restrict p x hp
    refine ⟨y, (flagCrossingPoint_insert_zero_iff X p y).mp (heq.symm ▸ hx), ?_⟩
    rw [← heq, sum_insertNth_zero_mul] at hz
    exact hz

/-- Zeroing one extra coordinate is the zero crossing of the row-augmented matrix. -/
theorem flagZeroBit_prepend {r n : ℕ} (X : Matrix (Fin r) (Fin n) ℝ) (z : Fin n → ℝ) :
    flagZeroBit (flagPrependRow z X) =
      if ∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) = 0 then 1 else 0 := by
  have heq (x : Fin n → ℝ) : flagPrependRow z X *ᵥ x = 0 ↔
      X *ᵥ x = 0 ∧ (∑ i, x i * z i) = 0 := by
    rw [flagPrependRow_mulVec]
    constructor
    · intro h
      refine ⟨funext fun i => congrFun h i.succ, ?_⟩
      have hh : (∑ i, z i * x i) = 0 := congrFun h 0
      simpa only [mul_comm] using hh
    · rintro ⟨hX, hz⟩
      have hz' : (∑ i, z i * x i) = 0 := by simpa only [mul_comm] using hz
      rw [hX, hz']
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
  have hiff : (∃ x, flagCrossingPoint (flagPrependRow z X) x) ↔
      (∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) = 0) := by
    simp only [flagCrossingPoint, heq]
    aesop
  unfold flagZeroBit
  rw [hiff]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.FlagCrossingSymmetry` -/


/-!
# Invariance and the antipodal crossing identity

Crossing indicators are independent of how finite vertices are numbered.
For a simplex with a unique coordinate crossing and nonzero next height,
its zero-crossing indicator is the sum of positive-crossing indicators for
itself and its global negative. This is the second local identity needed
for the hemisphere recurrence; no global odd-map obstruction is claimed.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

/-- Reindexing vertices preserves the coordinate image of reindexed coefficients. -/
theorem flag_mulVec_reindex {ρ ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ρ ι ℝ) (e : κ ≃ ι) (x : ι → ℝ) :
    X.submatrix id e *ᵥ (x ∘ e) = X *ᵥ x := by
  funext r
  exact e.sum_comp (fun i => X r i * x i)

/-- Feasibility depends on the vertex set, not its numbering. -/
theorem flagCrossingPoint_reindex_iff {ρ ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ρ ι ℝ) (e : κ ≃ ι) (x : ι → ℝ) :
    flagCrossingPoint (X.submatrix id e) (x ∘ e) ↔ flagCrossingPoint X x := by
  unfold flagCrossingPoint
  rw [flag_mulVec_reindex]
  have hs : ∑ i, (x ∘ e) i = ∑ i, x i := e.sum_comp x
  rw [hs]
  constructor
  · rintro ⟨hm, hX, hx⟩
    exact ⟨hm, hX, fun i => by simpa using hx (e.symm i)⟩
  · rintro ⟨hm, hX, hx⟩
    exact ⟨hm, hX, fun i => hx (e i)⟩

/-- Zero-crossing indicators are invariant under any vertex equivalence. -/
theorem flagZeroBit_reindex {ρ ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ρ ι ℝ) (e : κ ≃ ι) :
    flagZeroBit (X.submatrix id e) = flagZeroBit X := by
  have hiff : (∃ y, flagCrossingPoint (X.submatrix id e) y) ↔
      (∃ x, flagCrossingPoint X x) := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ e.symm, (flagCrossingPoint_reindex_iff X e _).mp ?_⟩
      simpa only [Function.comp_def, Equiv.symm_apply_apply] using hy
    · rintro ⟨x, hx⟩
      exact ⟨x ∘ e, (flagCrossingPoint_reindex_iff X e x).mpr hx⟩
  simp only [flagZeroBit, hiff]

/-- Positive-crossing indicators are invariant under simultaneous vertex reindexing. -/
theorem flagPositiveBit_reindex {ρ ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) (e : κ ≃ ι) :
    flagPositiveBit (X.submatrix id e) (z ∘ e) = flagPositiveBit X z := by
  have hiff : flagHasPositiveCrossing (X.submatrix id e) (z ∘ e) ↔
      flagHasPositiveCrossing X z := by
    constructor
    · rintro ⟨y, hy, hz⟩
      refine ⟨y ∘ e.symm, (flagCrossingPoint_reindex_iff X e _).mp ?_, ?_⟩
      · simpa only [Function.comp_def, Equiv.symm_apply_apply] using hy
      · have hs := e.sum_comp (fun i => (y ∘ e.symm) i * z i)
        rw [← hs]
        simpa only [Function.comp_def, Equiv.symm_apply_apply] using hz
    · rintro ⟨x, hx, hz⟩
      refine ⟨x ∘ e, (flagCrossingPoint_reindex_iff X e x).mpr hx, ?_⟩
      have hs := e.sum_comp (fun i => x i * z i)
      exact hs.symm ▸ hz
  simp only [flagPositiveBit, hiff]

/-- Negating every vertex image leaves the zero-coordinate equations unchanged. -/
theorem flagCrossingPoint_neg_iff {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (x : ι → ℝ) :
    flagCrossingPoint (-X) x ↔ flagCrossingPoint X x := by
  simp [flagCrossingPoint, Matrix.neg_mulVec]

theorem flagZeroBit_neg {ρ ι : Type*} [Fintype ι] (X : Matrix ρ ι ℝ) :
    flagZeroBit (-X) = flagZeroBit X := by
  simp only [flagZeroBit, flagCrossingPoint_neg_iff]

/-- Positive height on the antipodal simplex is negative height on the original. -/
theorem flagPositiveCrossing_neg_iff {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) :
    flagHasPositiveCrossing (-X) (-z) ↔
      ∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) < 0 := by
  simp [flagHasPositiveCrossing, flagCrossingPoint_neg_iff, Finset.sum_neg_distrib]

/-- A nonsingular mass-augmented square system has at most one crossing. -/
theorem flagCrossingPoint_unique {k : ℕ}
    (X : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (hdet : (flagPrependRow (fun _ => 1) X).det ≠ 0)
    (x y : Fin (k + 1) → ℝ) (hx : flagCrossingPoint X x) (hy : flagCrossingPoint X y) :
    x = y := by
  have hu : IsUnit (flagPrependRow (fun _ => 1) X) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  simp only [flagPrependRow_mulVec, one_mul, hx.1, hy.1, hx.2.1, hy.2.1]

/-- A nonsingular height-augmented square system forbids a zero-height crossing. -/
theorem flagCrossingPoint_height_ne_zero {k : ℕ}
    (X : Matrix (Fin k) (Fin (k + 1)) ℝ) (z : Fin (k + 1) → ℝ)
    (hdet : (flagPrependRow z X).det ≠ 0)
    (x : Fin (k + 1) → ℝ) (hx : flagCrossingPoint X x) :
    ∑ i, x i * z i ≠ 0 := by
  intro hz
  have hu : IsUnit (flagPrependRow z X) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have heq : x = 0 := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr hu
    have hz' : (∑ i, z i * x i) = 0 := by simpa only [mul_comm] using hz
    rw [Matrix.mulVec_zero, flagPrependRow_mulVec, hz', hx.2.1]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hm := hx.1
  simp [heq] at hm

/-- The local antipodal identity q = alpha + A*alpha, including no-crossing cases. -/
theorem flag_antipodal_crossing_parity {k : ℕ}
    (X : Matrix (Fin k) (Fin (k + 1)) ℝ) (z : Fin (k + 1) → ℝ)
    (hmass : (flagPrependRow (fun _ => 1) X).det ≠ 0)
    (hheight : (flagPrependRow z X).det ≠ 0) :
    flagZeroBit X = flagPositiveBit X z + flagPositiveBit (-X) (-z) := by
  by_cases hfeas : ∃ x, flagCrossingPoint X x
  · obtain ⟨x, hx⟩ := hfeas
    have hp : flagHasPositiveCrossing X z ↔ 0 < ∑ i, x i * z i := by
      constructor
      · rintro ⟨y, hy, hz⟩
        have heq := flagCrossingPoint_unique X hmass y x hy hx
        simpa only [heq] using hz
      · intro hz
        exact ⟨x, hx, hz⟩
    have hn : flagHasPositiveCrossing (-X) (-z) ↔ (∑ i, x i * z i) < 0 := by
      rw [flagPositiveCrossing_neg_iff]
      constructor
      · rintro ⟨y, hy, hz⟩
        have heq := flagCrossingPoint_unique X hmass y x hy hx
        simpa only [heq] using hz
      · intro hz
        exact ⟨x, hx, hz⟩
    have hz := flagCrossingPoint_height_ne_zero X z hheight x hx
    have he : ∃ x, flagCrossingPoint X x := ⟨x, hx⟩
    simp only [flagZeroBit, ite_eq_left he, flagPositiveBit, hp, hn]
    rcases lt_or_gt_of_ne hz with hz | hz <;> simp [hz, not_lt.mpr (le_of_lt hz)]
  · have hp : ¬ flagHasPositiveCrossing X z := fun ⟨x, hx, _⟩ => hfeas ⟨x, hx⟩
    have hn : ¬ flagHasPositiveCrossing (-X) (-z) := by
      rw [flagPositiveCrossing_neg_iff]
      exact fun ⟨x, hx, _⟩ => hfeas ⟨x, hx⟩
    simp [flagZeroBit, flagPositiveBit, hfeas, hp, hn]

/-- With one vertex and no coordinate equations, the base crossing count is one. -/
theorem flagZeroBit_single_vertex (X : Matrix (Fin 0) (Fin 1) ℝ) :
    flagZeroBit X = 1 := by
  have h : ∃ x, flagCrossingPoint X x := by
    refine ⟨fun _ => 1, ?_, ?_, ?_⟩
    · simp
    · funext i
      exact Fin.elim0 i
    · intro i
      exact zero_le_one
  exact ite_eq_left h

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonFaceEnumeration` -/


/-!
# Enumerating actual hexagon faces and their deleted faces

Crossing indicators will use the subtype of vertices in a face. These
equivalences connect that subtype to the finite column indices of the
local matrix theorems, including deletion and the genuine antipodal map.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Any prescribed cardinality supplies an enumeration of a face. -/
noncomputable def hexFaceEnumeration {r n : ℕ} (f : Finset (HexVertex r))
    (hf : f.card = n) : Fin n ≃ f := (f.equivFinOfCardEq hf).symm

/-- Delete one index from an enumeration and one vertex from the actual face. -/
noncomputable def hexFaceEraseEnumeration {r n : ℕ} {f : Finset (HexVertex r)}
    (e : Fin (n + 1) ≃ f) (i : Fin (n + 1)) : Fin n ≃ (f.erase (e i).val) :=
  Equiv.ofBijective
    (fun j => ⟨(e (i.succAbove j)).val, Finset.mem_erase.mpr
      ⟨fun h => i.succAbove_ne j (e.injective (Subtype.ext h)), (e _).property⟩⟩) (by
    constructor
    · intro j l h
      have hv : (e (i.succAbove j)).val = (e (i.succAbove l)).val :=
        congrArg (fun v : (f.erase (e i).val) => v.val) h
      exact Fin.succAbove_right_injective (e.injective (Subtype.ext hv))
    · intro v
      obtain ⟨hvne, hvf⟩ := Finset.mem_erase.mp v.property
      obtain ⟨j, hj⟩ := e.surjective ⟨v.val, hvf⟩
      rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨l, rfl⟩
      · subst j
        exact (hvne (congrArg Subtype.val hj).symm).elim
      · refine ⟨l, Subtype.ext ?_⟩
        exact congrArg (fun w : f => w.val) hj)

theorem hexFaceEraseEnumeration_val {r n : ℕ} {f : Finset (HexVertex r)}
    (e : Fin (n + 1) ≃ f) (i : Fin (n + 1)) (j : Fin n) :
    (hexFaceEraseEnumeration e i j).val = (e (i.succAbove j)).val := rfl

/-- The genuine antipode gives a bijection of face vertex subtypes. -/
noncomputable def hexFaceAntipodalEquiv {r : ℕ} (f : Finset (HexVertex r)) :
    f ≃ (f.image hexVertexOpposite) :=
  Equiv.ofBijective
    (fun v => ⟨hexVertexOpposite v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩) (by
    constructor
    · intro v w h
      exact Subtype.ext ((hexVertexOpposite_involutive r).injective (congrArg Subtype.val h))
    · intro v
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp v.property
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩)

theorem hexFaceAntipodalEquiv_val {r : ℕ} (f : Finset (HexVertex r)) (v : f) :
    (hexFaceAntipodalEquiv f v).val = hexVertexOpposite v.val := rfl

/-- Summing over enumerated deletions is the actual simplicial coboundary. -/
theorem hexCoboundary_eq_sum_enumeration {r n : ℕ} (a : HexModTwoChain r)
    (f : Finset (HexVertex r)) (e : Fin n ≃ f) :
    hexCoboundary a f = ∑ i : Fin n, a (f.erase (e i).val) := by
  have h := e.sum_comp (fun v : f => a (f.erase v.val))
  change (∑ v ∈ f, a (f.erase v)) = _
  rw [← Finset.sum_attach f (fun v => a (f.erase v))]
  exact h.symm

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonFlagCochains` -/


/-!
# Coordinate-crossing cochains on actual hexagon faces

Coordinates are stored as a sequence. The first k rows are written in
reverse order so adding the next coordinate is exactly row prepending.
This is the same coordinate flag, with no change to the zero equations.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

def hexFlagMatrix {r : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    (f : Finset (HexVertex r)) : Matrix (Fin k) f ℝ :=
  Matrix.of (fun i v => p v.val i.rev.val)

noncomputable def hexFlagZero {r : ℕ} (p : HexVertex r → ℕ → ℝ)
    (k : ℕ) : HexModTwoChain r := fun f => flagZeroBit (hexFlagMatrix p k f)

noncomputable def hexFlagPositive {r : ℕ} (p : HexVertex r → ℕ → ℝ)
    (k : ℕ) : HexModTwoChain r :=
  fun f => flagPositiveBit (hexFlagMatrix p k f) (fun v => p v.val k)

/-- The matrix whose columns are any chosen listing of the actual face. -/
def hexFlagEnumMatrix {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) : Matrix (Fin k) (Fin n) ℝ :=
  (hexFlagMatrix p k f).submatrix id e

theorem hexFlagZero_eq_enumeration {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    (f : Finset (HexVertex r)) (e : Fin n ≃ f) :
    hexFlagZero p k f = flagZeroBit (hexFlagEnumMatrix p k e) :=
  (flagZeroBit_reindex (hexFlagMatrix p k f) e).symm

theorem hexFlagPositive_eq_enumeration {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    (f : Finset (HexVertex r)) (e : Fin n ≃ f) :
    hexFlagPositive p k f =
      flagPositiveBit (hexFlagEnumMatrix p k e) (fun j => p (e j).val k) :=
  (flagPositiveBit_reindex (hexFlagMatrix p k f) (fun v => p v.val k) e).symm

/-- Adding the next flag coordinate is row prepending in reverse row order. -/
theorem hexFlagEnumMatrix_succ {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) :
    hexFlagEnumMatrix p (k + 1) e =
      flagPrependRow (fun j => p (e j).val k) (hexFlagEnumMatrix p k e) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [hexFlagEnumMatrix, hexFlagMatrix, flagPrependRow]
  · simp [hexFlagEnumMatrix, hexFlagMatrix, flagPrependRow]

/-- Removing a column is precisely the matrix of the vertex-deleted face. -/
theorem hexFlagEnumMatrix_erase {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    {f : Finset (HexVertex r)} (e : Fin (n + 1) ≃ f) (i : Fin (n + 1)) :
    hexFlagEnumMatrix p k (hexFaceEraseEnumeration e i) =
      (hexFlagEnumMatrix p k e).submatrix id i.succAbove := rfl

theorem hexFlagPositive_erase {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    {f : Finset (HexVertex r)} (e : Fin (n + 1) ≃ f) (i : Fin (n + 1)) :
    hexFlagPositive p k (f.erase (e i).val) =
      flagPositiveBit ((hexFlagEnumMatrix p k e).submatrix id i.succAbove)
        (fun j => p (e (i.succAbove j)).val k) := by
  rw [hexFlagPositive_eq_enumeration p k _ (hexFaceEraseEnumeration e i)]
  rfl

/-- Under odd vertex data, the actual antipodal face has the negative matrix. -/
theorem hexFlagPositive_antipodal {r : ℕ} (p : HexVertex r → ℕ → ℝ)
    (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j)
    (k : ℕ) (f : Finset (HexVertex r)) :
    hexFlagPositive p k (f.image hexVertexOpposite) =
      flagPositiveBit (-hexFlagMatrix p k f) (fun v => -p v.val k) := by
  unfold hexFlagPositive
  rw [← flagPositiveBit_reindex _ _ (hexFaceAntipodalEquiv f)]
  congr 1
  · ext i v
    exact hp v.val i.rev.val
  · funext v
    exact hp v.val k

/-- One vertex always meets the flag with zero coordinate equations. -/
theorem hexFlagZero_vertex {r : ℕ} (p : HexVertex r → ℕ → ℝ) (v : HexVertex r) :
    hexFlagZero p 0 {v} = 1 := by
  rw [hexFlagZero_eq_enumeration p 0 _ (hexFaceEnumeration (n := 1) {v} (by simp))]
  exact flagZeroBit_single_vertex _

/-- Nonzero q is an actual barycentric zero of all the first k coordinates. -/
theorem hexFlagZero_ne_zero_iff {r : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    (f : Finset (HexVertex r)) :
    hexFlagZero p k f ≠ 0 ↔ ∃ x : f → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧
        ∀ j : Fin k, (∑ v, x v * p v.val j.val) = 0 := by
  classical
  have he (x : f → ℝ) : hexFlagMatrix p k f *ᵥ x = 0 ↔
      ∀ j : Fin k, (∑ v, x v * p v.val j.val) = 0 := by
    constructor
    · intro h j
      have h' := congrFun h j.rev
      change (∑ v, p v.val j.rev.rev.val * x v) = 0 at h'
      rw [Fin.rev_rev] at h'
      simpa only [mul_comm] using h'
    · intro h
      funext i
      change (∑ v, p v.val i.rev.val * x v) = 0
      simpa only [mul_comm] using h i.rev
  simp only [hexFlagZero, flagZeroBit, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not, flagCrossingPoint, he]
  aesop

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.FlagBoundaryParity` -/


/-!
# The local coordinate-flag boundary identity

Under the explicit finite minor conditions, the zero-crossing indicator
of a simplex is the sum of positive-crossing indicators of all of its
codimension-one faces over ZMod 2. Empty slices are included. This is a
local matrix theorem; transport to the hexagon face chains and removal
of general position remain separate tasks.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

/-- A generic boundary face has at most one barycentric coordinate crossing. -/
theorem flagBoundaryPoint_unique {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (p : Fin (r + 2))
    (hdet : (sliceDeleteColumn (flagConstraintMatrix X) p).det ≠ 0)
    (x y : Fin (r + 2) → ℝ)
    (hx : flagCrossingPoint X x) (hy : flagCrossingPoint X y)
    (hxp : x p = 0) (hyp : y p = 0) : x = y := by
  have hx' := (flagConstraintMatrix_eq_rhs_iff X x).mpr ⟨hx.1, hx.2.1⟩
  have hy' := (flagConstraintMatrix_eq_rhs_iff X y).mpr ⟨hy.1, hy.2.1⟩
  have hk : flagConstraintMatrix X *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hx', hy', sub_self]
  have hp : (x - y) p = 0 := by simp [hxp, hyp]
  exact sub_eq_zero.mp (sliceMatrix_kernel_eq_zero_of_coord_zero
    (flagConstraintMatrix X) p hdet (x - y) hk hp)

/-- The local identity q = delta alpha, with one term per actual deleted-column
face and with no nonemptiness assumption on the slice. -/
theorem flag_local_boundary_parity {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hG : FlagSliceGeneric X z) :
    flagZeroBit (flagPrependRow z X) =
      ∑ i : Fin (r + 2), flagPositiveBit (X.submatrix id i.succAbove)
        (fun j => z (i.succAbove j)) := by
  by_cases hfeas : ∃ x, flagSlicePoint X x
  · obtain ⟨a, w, L, U, p, n, hLU, hpn, hline, hI, hLp, hUn,
      _, hboundary, hd, hL, hU⟩ := exists_flagSlice_interval X z hG hfeas
    have hLl := (hline (sliceCoeff a w L)).mpr ⟨L, rfl⟩
    have hUl := (hline (sliceCoeff a w U)).mpr ⟨U, rfl⟩
    have hl : flagCrossingPoint X (sliceCoeff a w L) :=
      ⟨hLl.1, hLl.2, (hI L).mpr ⟨le_rfl, hLU.le⟩⟩
    have hu : flagCrossingPoint X (sliceCoeff a w U) :=
      ⟨hUl.1, hUl.2, (hI U).mpr ⟨hLU.le, le_rfl⟩⟩
    have hface (i : Fin (r + 2)) : flagHasBoundaryCrossing X z i ↔
        (i = p ∧ 0 < sliceHeight a w z L) ∨ (i = n ∧ 0 < sliceHeight a w z U) := by
      constructor
      · rintro ⟨x, hx, hxi, hpos⟩
        obtain ⟨t, rfl⟩ := (hline x).mp ⟨hx.1, hx.2.1⟩
        obtain rfl | rfl := (hboundary t).mp ⟨hx.2.2, i, hxi⟩
        · exact Or.inl ⟨(hLp i).mp hxi, hpos⟩
        · exact Or.inr ⟨(hUn i).mp hxi, hpos⟩
      · rintro (⟨rfl, hpos⟩ | ⟨rfl, hpos⟩)
        · exact ⟨sliceCoeff a w L, hl, (hLp _).mpr rfl, hpos⟩
        · exact ⟨sliceCoeff a w U, hu, (hUn _).mpr rfl, hpos⟩
    have hbit (i : Fin (r + 2)) :
        (if flagHasBoundaryCrossing X z i then (1 : ZMod 2) else 0) =
          (if i = p then positiveBit (sliceHeight a w z L) else 0) +
          (if i = n then positiveBit (sliceHeight a w z U) else 0) := by
      rw [hface]
      by_cases hip : i = p
      · subst i
        simp [hpn, positiveBit]
      · by_cases hin : i = n
        · subst i
          simp [hip, positiveBit]
        · simp [hip, hin]
    have hcount : (∑ i : Fin (r + 2),
        flagPositiveBit (X.submatrix id i.succAbove) (fun j => z (i.succAbove j))) =
        positiveBit (sliceHeight a w z L) + positiveBit (sliceHeight a w z U) := by
      simp only [flagPositiveBit, flagPositiveCrossing_face_iff, hbit]
      rw [Finset.sum_add_distrib]
      simp
    have hex : (∃ t, sliceFeasible a w t ∧ sliceHeight a w z t = 0) ↔
        (∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) = 0) := by
      constructor
      · rintro ⟨t, ht, hz⟩
        have heq := (hline (sliceCoeff a w t)).mpr ⟨t, rfl⟩
        exact ⟨sliceCoeff a w t, ⟨heq.1, heq.2, ht⟩, hz⟩
      · rintro ⟨x, hx, hz⟩
        obtain ⟨t, rfl⟩ := (hline x).mp ⟨hx.1, hx.2.1⟩
        exact ⟨t, hx.2.2, hz⟩
    rw [hcount, flagZeroBit_prepend]
    have hpar := sliceHeight_endpoint_parity a w z hLU hI hd hL hU
    rw [hex] at hpar
    exact hpar.symm
  · have hz : ¬ ∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) = 0 := by
      rintro ⟨x, hx, _⟩
      exact hfeas ⟨x, hx⟩
    have hf (i : Fin (r + 2)) : ¬ flagHasBoundaryCrossing X z i := by
      rintro ⟨x, hx, _, _⟩
      exact hfeas ⟨x, hx⟩
    simp [flagZeroBit_prepend, flagPositiveBit, flagPositiveCrossing_face_iff, hz, hf]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonGenericZero` -/


/-!
# A barycentric zero for generic odd vertex configurations

The hypotheses below are concrete finite determinant conditions, not the
cochain identities to be proved. We derive those identities from the local
matrix theorems and then use the verified hemisphere tower. Removing the
determinant hypotheses remains a separate perturbation problem.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

/-- The finite general-position conditions used on the actual hexagon faces.
All enumerations are allowed; this makes the condition independent of choices.
Only coordinate heights strictly below 2r-1 occur. -/
structure HexFlagGeneric {r : ℕ} (p : HexVertex r → ℕ → ℝ) : Prop where
  boundary : ∀ k, k + 1 < 2 * r → ∀ f ∈ (hexFanComplex r).faces,
    ∀ e : Fin (k + 2) ≃ f,
      FlagSliceGeneric (hexFlagEnumMatrix p k e) (fun j => p (e j).val k)
  mass : ∀ k, k + 1 < 2 * r → ∀ f ∈ (hexFanComplex r).faces,
    ∀ e : Fin (k + 1) ≃ f,
      (flagPrependRow (fun _ => 1) (hexFlagEnumMatrix p k e)).det ≠ 0
  height : ∀ k, k + 1 < 2 * r → ∀ f ∈ (hexFanComplex r).faces,
    ∀ e : Fin (k + 1) ≃ f,
      (flagPrependRow (fun j => p (e j).val k) (hexFlagEnumMatrix p k e)).det ≠ 0

/-- The local matrix boundary formula is the actual face coboundary formula. -/
theorem hexFlag_boundary_parity {r k : ℕ} (p : HexVertex r → ℕ → ℝ)
    (f : Finset (HexVertex r)) (e : Fin (k + 2) ≃ f)
    (hG : FlagSliceGeneric (hexFlagEnumMatrix p k e) (fun j => p (e j).val k)) :
    hexFlagZero p (k + 1) f = hexCoboundary (hexFlagPositive p k) f := by
  rw [hexFlagZero_eq_enumeration p (k + 1) f e, hexFlagEnumMatrix_succ,
    flag_local_boundary_parity _ _ hG, hexCoboundary_eq_sum_enumeration _ f e]
  apply Finset.sum_congr rfl
  intro i _
  exact (hexFlagPositive_erase p k e i).symm

/-- Oddness of the vertex images turns matrix negation into the actual antipode. -/
theorem hexFlag_antipodal_parity {r k : ℕ} (p : HexVertex r → ℕ → ℝ)
    (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j)
    (f : Finset (HexVertex r)) (e : Fin (k + 1) ≃ f)
    (hmass : (flagPrependRow (fun _ => 1) (hexFlagEnumMatrix p k e)).det ≠ 0)
    (hheight : (flagPrependRow (fun j => p (e j).val k)
      (hexFlagEnumMatrix p k e)).det ≠ 0) :
    hexFlagZero p k f = hexFlagPositive p k f +
      hexAntipodalCochain (hexFlagPositive p k) f := by
  have hn : flagPositiveBit (-hexFlagEnumMatrix p k e) (-(fun j => p (e j).val k)) =
      hexFlagPositive p k (f.image hexVertexOpposite) := by
    rw [hexFlagPositive_antipodal p hp]
    exact flagPositiveBit_reindex (-hexFlagMatrix p k f) (fun v => -p v.val k) e
  rw [hexFlagZero_eq_enumeration p k f e,
    flag_antipodal_crossing_parity _ _ hmass hheight, hn,
    ← hexFlagPositive_eq_enumeration p k f e]
  rfl

/-- Supply the boundary input of the tower from the stated determinant conditions. -/
theorem HexFlagGeneric.boundary_identity {r : ℕ} {p : HexVertex r → ℕ → ℝ}
    (hG : HexFlagGeneric p) (k : ℕ) (hk : k + 1 < 2 * r)
    (f : Finset (HexVertex r)) (hf : f ∈ (hexFanComplex r).faces) (hcard : f.card = k + 2) :
    hexFlagZero p (k + 1) f = hexCoboundary (hexFlagPositive p k) f :=
  hexFlag_boundary_parity p f (hexFaceEnumeration f hcard)
    (hG.boundary k hk f hf (hexFaceEnumeration f hcard))

/-- Supply the antipodal input of the tower from oddness and nonzero determinants. -/
theorem HexFlagGeneric.antipodal_identity {r : ℕ} {p : HexVertex r → ℕ → ℝ}
    (hG : HexFlagGeneric p) (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j)
    (k : ℕ) (hk : k + 1 < 2 * r) (f : Finset (HexVertex r))
    (hf : f ∈ (hexFanComplex r).faces) (hcard : f.card = k + 1) :
    hexFlagZero p k f = hexFlagPositive p k f +
      hexAntipodalCochain (hexFlagPositive p k) f :=
  hexFlag_antipodal_parity p hp f (hexFaceEnumeration f hcard)
    (hG.mass k hk f hf (hexFaceEnumeration f hcard))
    (hG.height k hk f hf (hexFaceEnumeration f hcard))

/-- The geometric crossing cochain evaluates to one in every degree of the tower. -/
theorem hexFlagGeneric_parity_one {r : ℕ} (p : HexVertex r → ℕ → ℝ)
    (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j) (hG : HexFlagGeneric p)
    {k : ℕ} (hk : k < 2 * r) :
    hexCochainEval (hexFlagZero p k) (hexHemisphereTower r k) = 1 :=
  hexHemisphereTower_parity_one (hexFlagZero p) (hexFlagPositive p)
    (hexFlagZero_vertex p) hG.boundary_identity (hG.antipodal_identity hp) hk

/-- An actual facet has a nonnegative mass-one zero of all first 2r-1 coordinates. -/
theorem hexFlagGeneric_exists_zero {r : ℕ} (hr : 0 < r) (p : HexVertex r → ℕ → ℝ)
    (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j) (hG : HexFlagGeneric p) :
    ∃ s : Fin r → Fin 6, ∃ x : (hexFacet s) → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧
        ∀ j : Fin (2 * r - 1), (∑ v, x v * p v.val j.val) = 0 := by
  obtain ⟨s, hs⟩ := hexHemisphereTower_exists_top_crossing hr
    (hexFlagZero p) (hexFlagPositive p) (hexFlagZero_vertex p)
    hG.boundary_identity (hG.antipodal_identity hp)
  exact ⟨s, (hexFlagZero_ne_zero_iff p _ _).mp hs⟩

/-- Extend a finite-dimensional vertex image by zero; used only to index prefixes. -/
def hexFlagExtend {r m : ℕ} (p : HexVertex r → Fin m → ℝ) : HexVertex r → ℕ → ℝ :=
  fun v j => if h : j < m then p v ⟨j, h⟩ else 0

theorem hexFlagExtend_odd {r m : ℕ} (p : HexVertex r → Fin m → ℝ)
    (hp : ∀ v, p (hexVertexOpposite v) = -p v) :
    ∀ v j, hexFlagExtend p (hexVertexOpposite v) j = -hexFlagExtend p v j := by
  intro v j
  simp only [hexFlagExtend]
  split_ifs with h
  · exact congrFun (hp v) ⟨j, h⟩
  · simp

/-- In the actual target dimension, a generic odd vertex configuration has zero
in the convex hull of the image of some actual facet. -/
theorem hexGenericOdd_exists_barycentric_zero {r : ℕ} (hr : 0 < r)
    (p : HexVertex r → Fin (2 * r - 1) → ℝ)
    (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hG : HexFlagGeneric (hexFlagExtend p)) :
    ∃ s : Fin r → Fin 6, ∃ x : (hexFacet s) → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v • p v.val) = 0 := by
  obtain ⟨s, x, hm, hx, hz⟩ :=
    hexFlagGeneric_exists_zero hr (hexFlagExtend p) (hexFlagExtend_odd p hp) hG
  refine ⟨s, x, hm, hx, ?_⟩
  funext j
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hexFlagExtend, j.isLt] using hz j

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonZeroFree` -/


/-!
# Stability of configurations with no facet zero

Strict separation characterizes exclusion of zero from a finite convex hull.
The finitely many strict inequalities are open in the vertex images, so a
configuration without facet zeros remains so under small perturbations.
-/

namespace VCDimConvexBound

open scoped BigOperators Topology

theorem zero_not_mem_convexHull_range_iff_strict_positive {ι : Type*} [Fintype ι]
    {m : ℕ} (p : ι → Point m) :
    (0 : Point m) ∉ convexHull ℝ (Set.range p) ↔
      ∃ l : Point m →L[ℝ] ℝ, ∀ v, 0 < l (p v) := by
  constructor
  · intro h
    obtain ⟨l, u, hu, hl⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ _) ((Set.toFinite _).isClosed_convexHull ℝ) h
    refine ⟨l, fun v => ?_⟩
    simpa using hu.trans (hl _ (subset_convexHull ℝ _ (Set.mem_range_self v)))
  · rintro ⟨l, hl⟩ h
    have hs : convexHull ℝ (Set.range p) ⊆ {x | 0 < l x} := by
      apply convexHull_min _ (convex_halfSpace_gt ⟨l.map_add, l.map_smul⟩ 0)
      rintro _ ⟨v, rfl⟩
      exact hl v
    simpa using hs h

theorem isOpen_zero_not_mem_convexHull_range {ι : Type*} [Fintype ι] (m : ℕ) :
    IsOpen {p : ι → Point m | (0 : Point m) ∉ convexHull ℝ (Set.range p)} := by
  simp only [zero_not_mem_convexHull_range_iff_strict_positive,
    Set.ofPred_exists, Set.ofPred_forall]
  apply isOpen_iUnion
  intro l
  apply isOpen_iInter_of_finite
  intro v
  exact isOpen_lt continuous_const (l.continuous.comp (continuous_apply v))

/-- No maximal face has a nonnegative mass-one combination mapping to zero. -/
def HexZeroFree {r m : ℕ} (p : HexVertex r → Point m) : Prop :=
  ∀ s : Fin r → Fin 6,
    (0 : Point m) ∉ convexHull ℝ (Set.range (fun v : hexFacet s => p v.val))

theorem not_hexZeroFree_iff_barycentric_zero {r m : ℕ} (p : HexVertex r → Point m) :
    ¬ HexZeroFree p ↔ ∃ s : Fin r → Fin 6, ∃ x : (hexFacet s) → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v • p v.val) = 0 := by
  classical
  simp only [HexZeroFree, not_forall, not_not, mem_convexHull_range_iff_weights]
  aesop

theorem isOpen_hexZeroFree (r m : ℕ) :
    IsOpen {p : HexVertex r → Point m | HexZeroFree p} := by
  unfold HexZeroFree
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro s
  exact (isOpen_zero_not_mem_convexHull_range m).preimage
    (show Continuous (fun p : HexVertex r → Point m => fun v : hexFacet s => p v.val) by
      fun_prop)

/-- There is a uniform positive radius preserving exclusion of zero on every facet. -/
theorem HexZeroFree.exists_radius {r m : ℕ} {p : HexVertex r → Point m}
    (hp : HexZeroFree p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q, dist q p < ε → HexZeroFree q := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_hexZeroFree r m) p hp
  exact ⟨ε, hε, fun q hq => hball hq⟩

/-- The previously proved generic odd zero theorem rules out generic counterexamples. -/
theorem not_hexZeroFree_of_generic_odd {r : ℕ} (hr : 0 < r)
    (p : HexVertex r → Point (2 * r - 1))
    (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hG : HexFlagGeneric (hexFlagExtend p)) : ¬ HexZeroFree p :=
  (not_hexZeroFree_iff_barycentric_zero p).mpr
    (hexGenericOdd_exists_barycentric_zero hr p hp hG)

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.PolynomialAvoidance` -/


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


/-! ## Source module `VCDimConvexBound.HexagonOddParameters` -/


/-!
# Free coordinates for odd vertex configurations

Only vertices 0,1,2 in each color are free. Vertices 3,4,5 are their
negatives. Every odd configuration is recovered from these coordinates,
and every vertex coordinate is a signed variable polynomial.
-/

namespace VCDimConvexBound

abbrev HexOddVariable (r m : ℕ) := Fin r × Fin 3 × Fin m

def hexOddConfiguration {r m : ℕ} (a : HexOddVariable r m → ℝ) : HexVertex r → Point m :=
  fun v j => if h : v.2.val < 3 then a (v.1, ⟨v.2.val, h⟩, j)
    else -a (v.1, ⟨v.2.val - 3, by omega⟩, j)

def hexOddParameters {r m : ℕ} (p : HexVertex r → Point m) : HexOddVariable r m → ℝ :=
  fun a => p (a.1, Fin.castLE (by decide) a.2.1) a.2.2

theorem hexOddConfiguration_odd {r m : ℕ} (a : HexOddVariable r m → ℝ)
    (v : HexVertex r) :
    hexOddConfiguration a (hexVertexOpposite v) = -hexOddConfiguration a v := by
  rcases v with ⟨k, j⟩
  fin_cases j <;> funext l <;>
    simp [hexOddConfiguration, hexVertexOpposite, hexOpposite]

theorem continuous_hexOddConfiguration (r m : ℕ) :
    Continuous (@hexOddConfiguration r m) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro j
  dsimp only [hexOddConfiguration]
  split_ifs <;> fun_prop

theorem hexOddParameters_configuration {r m : ℕ} (a : HexOddVariable r m → ℝ) :
    hexOddParameters (hexOddConfiguration a) = a := by
  funext x
  rcases x with ⟨k, j, l⟩
  simp [hexOddParameters, hexOddConfiguration, j.isLt]

theorem hexOddConfiguration_parameters {r m : ℕ} (p : HexVertex r → Point m)
    (hp : ∀ v, p (hexVertexOpposite v) = -p v) :
    hexOddConfiguration (hexOddParameters p) = p := by
  funext v l
  rcases v with ⟨k, j⟩
  have h0 := congrFun (hp (k, 0)) l
  have h1 := congrFun (hp (k, 1)) l
  have h2 := congrFun (hp (k, 2)) l
  simp only [hexVertexOpposite, hexOpposite, Pi.neg_apply] at h0 h1 h2
  fin_cases j <;> simp [hexOddConfiguration, hexOddParameters]
  · exact h0.symm
  · exact h1.symm
  · exact h2.symm

theorem hexOddConfiguration_injective (r m : ℕ) :
    Function.Injective (@hexOddConfiguration r m) := by
  intro a b h
  simpa only [hexOddParameters_configuration] using congrArg hexOddParameters h

/-- Each actual vertex coordinate is a signed variable in the free parameters. -/
noncomputable def hexOddCoordinatePolynomial {r m : ℕ} (v : HexVertex r) (j : Fin m) :
    MvPolynomial (HexOddVariable r m) ℝ :=
  if h : v.2.val < 3 then MvPolynomial.X (v.1, ⟨v.2.val, h⟩, j)
    else -MvPolynomial.X (v.1, ⟨v.2.val - 3, by omega⟩, j)

theorem eval_hexOddCoordinatePolynomial {r m : ℕ} (a : HexOddVariable r m → ℝ)
    (v : HexVertex r) (j : Fin m) :
    MvPolynomial.eval a (hexOddCoordinatePolynomial v j) = hexOddConfiguration a v j := by
  simp only [hexOddCoordinatePolynomial, hexOddConfiguration]
  split_ifs <;> simp

theorem hexOddCoordinatePolynomial_opposite {r m : ℕ} (v : HexVertex r) (j : Fin m) :
    hexOddCoordinatePolynomial (hexVertexOpposite v) j = -hexOddCoordinatePolynomial v j := by
  apply MvPolynomial.funext
  intro a
  simp only [map_neg, eval_hexOddCoordinatePolynomial]
  exact congrFun (hexOddConfiguration_odd a v) j

/-- Any finitely many genuinely nonzero polynomial conditions can be met by a
nearby odd configuration while retaining the absence of zeros on all facets. -/
theorem exists_odd_zeroFree_polynomial_perturbation {r m : ℕ} {ι : Type*} [Fintype ι]
    (p : HexVertex r → Point m) (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hz : HexZeroFree p) (P : ι → MvPolynomial (HexOddVariable r m) ℝ)
    (hP : ∀ i, P i ≠ 0) (U : Set (HexVertex r → Point m)) (hU : IsOpen U) (hpu : p ∈ U) :
    ∃ a : HexOddVariable r m → ℝ,
      hexOddConfiguration a ∈ U ∧ HexZeroFree (hexOddConfiguration a) ∧
        ∀ i, MvPolynomial.eval a (P i) ≠ 0 := by
  let V := hexOddConfiguration ⁻¹' (U ∩ {q | HexZeroFree q})
  have hV : IsOpen V :=
    (hU.inter (isOpen_hexZeroFree r m)).preimage (continuous_hexOddConfiguration r m)
  have hpa : hexOddParameters p ∈ V := by
    change hexOddConfiguration (hexOddParameters p) ∈ U ∩ {q | HexZeroFree q}
    rw [hexOddConfiguration_parameters p hp]
    exact ⟨hpu, hz⟩
  obtain ⟨a, ha, hne⟩ := exists_mvPolynomial_family_ne_zero_mem_open P hP V hV _ hpa
  exact ⟨a, ha.1, ha.2, hne⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonOddFaceExtension` -/


/-!
# Prescribing arbitrary images on a face while preserving oddness

A face contains no antipodal pair. Consequently its vertex images are
independent free data inside the space of all odd configurations. This is
the input needed to prove that determinant polynomials are not identically zero.
-/

namespace VCDimConvexBound

theorem hexFace_no_antipodal {r : ℕ} (f : Finset (HexVertex r))
    (hf : f ∈ (hexFanComplex r).faces) :
    ∀ v ∈ f, hexVertexOpposite v ∉ f := by
  obtain ⟨_, s, hs⟩ := hf
  intro v hv hw
  exact hexVertexOpposite_not_mem_facet s v (hs hv) (hs hw)

/-- Extend arbitrary face data to its antipode by negation, and use zero elsewhere. -/
def hexExtendOddFace {r m : ℕ} (f : Finset (HexVertex r)) (b : f → Point m) :
    HexVertex r → Point m := fun v =>
  if h : v ∈ f then b ⟨v, h⟩
  else if hA : hexVertexOpposite v ∈ f then -b ⟨hexVertexOpposite v, hA⟩ else 0

theorem hexExtendOddFace_agrees {r m : ℕ} (f : Finset (HexVertex r)) (b : f → Point m)
    (v : f) : hexExtendOddFace f b v.val = b v := by
  simp [hexExtendOddFace, v.property]

theorem hexExtendOddFace_odd {r m : ℕ} (f : Finset (HexVertex r))
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (b : f → Point m) (v : HexVertex r) :
    hexExtendOddFace f b (hexVertexOpposite v) = -hexExtendOddFace f b v := by
  by_cases hv : v ∈ f
  · have hA := hf v hv
    simp [hexExtendOddFace, hv, hA, hexVertexOpposite_involutive r v]
  · by_cases hA : hexVertexOpposite v ∈ f <;>
      simp [hexExtendOddFace, hv, hA, hexVertexOpposite_involutive r v]

/-- Every prescribed image on a face can be realized by the free odd parameters. -/
theorem exists_hexOddParameters_agree_on_face {r m : ℕ} (f : Finset (HexVertex r))
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (b : f → Point m) :
    ∃ a : HexOddVariable r m → ℝ, ∀ v : f, hexOddConfiguration a v.val = b v := by
  refine ⟨hexOddParameters (hexExtendOddFace f b), ?_⟩
  rw [hexOddConfiguration_parameters _ (hexExtendOddFace_odd f hf b)]
  exact hexExtendOddFace_agrees f b

/-- Arbitrary square coordinate matrices can be prescribed on distinct face vertices. -/
theorem exists_hexOddParameters_face_matrix {r m n : ℕ} (f : Finset (HexVertex r))
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (e : Fin n ≃ f)
    (ρ : Fin n ↪ Fin m) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ a : HexOddVariable r m → ℝ,
      ∀ i j, hexOddConfiguration a (e j).val (ρ i) = M i j := by
  let b : f → Point m := fun v => Function.extend ρ (fun i => M i (e.symm v)) 0
  obtain ⟨a, ha⟩ := exists_hexOddParameters_agree_on_face f hf b
  refine ⟨a, fun i j => ?_⟩
  rw [ha (e j)]
  simp [b, ρ.injective.extend_apply]

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonOddMinorPolynomials` -/


/-!
# Nonzero determinant polynomials in the odd configuration parameters

Rows select distinct coordinates, with an optional constant mass row.
Columns select every vertex of a finite set containing no antipodal pair.
Arbitrary face data supply an explicit determinant-one evaluation, so these
polynomials are genuinely nonzero even with the global oddness constraint.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

/-- Replacing one row of the identity by all ones still has determinant one. -/
theorem det_identity_updateRow_ones {n : ℕ} (i : Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun _ => 1)).det = 1 := by
  have hs : (∑ j : Fin n, (1 : Matrix (Fin n) (Fin n) ℝ) j) =
      (fun _ => 1) := by
    funext k
    change (∑ j : Fin n, fun l : Fin n => if j = l then (1 : ℝ) else 0) k = 1
    simp [Finset.sum_apply]
  simpa only [one_smul, hs, Matrix.det_one] using
    Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) ℝ) i (fun _ => 1)

/-- Prescribe a square matrix whose selected constant row is already all ones. -/
theorem exists_hexOddParameters_augmented_face_matrix {r m n : ℕ}
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i, ρ i = none → ∀ j, M i j = 1) :
    ∃ a : HexOddVariable r m → ℝ,
      ∀ i j, (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l) = M i j := by
  let b : f → Point m := fun v l =>
    Function.extend ρ (fun i => M i (e.symm v)) 0 (some l)
  obtain ⟨a, ha⟩ := exists_hexOddParameters_agree_on_face f hf b
  refine ⟨a, fun i j => ?_⟩
  cases hi : ρ i with
  | none => exact (hM i hi j).symm
  | some l =>
    simp only [Option.elim_some]
    rw [ha (e j)]
    change Function.extend ρ (fun i => M i (e.symm (e j))) 0 (some l) = M i j
    rw [← hi, ρ.injective.extend_apply, e.symm_apply_apply]

/-- Every augmented minor pattern has a determinant-one realization by odd data. -/
theorem exists_hexOddParameters_augmented_det_one {r m n : ℕ}
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)) :
    ∃ a : HexOddVariable r m → ℝ,
      (Matrix.of (fun i j => (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l))).det = 1 := by
  classical
  by_cases hnone : ∃ i, ρ i = none
  · obtain ⟨i₀, hi₀⟩ := hnone
    let M : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i₀ (fun _ => 1)
    have hM : ∀ i, ρ i = none → ∀ j, M i j = 1 := by
      intro i hi j
      have he : i = i₀ := ρ.injective (hi.trans hi₀.symm)
      subst i
      simp [M]
    obtain ⟨a, ha⟩ := exists_hexOddParameters_augmented_face_matrix f hf e ρ M hM
    refine ⟨a, ?_⟩
    have he : Matrix.of (fun i j => (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l)) = M :=
      Matrix.ext ha
    rw [he]
    exact det_identity_updateRow_ones i₀
  · obtain ⟨a, ha⟩ := exists_hexOddParameters_augmented_face_matrix f hf e ρ
      (1 : Matrix (Fin n) (Fin n) ℝ) (fun i hi => (hnone ⟨i, hi⟩).elim)
    refine ⟨a, ?_⟩
    rw [show Matrix.of (fun i j => (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) from Matrix.ext ha, Matrix.det_one]

noncomputable def hexOddMinorPolynomial {r m n : ℕ} (f : Finset (HexVertex r))
    (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)) : MvPolynomial (HexOddVariable r m) ℝ :=
  (Matrix.of (fun i j => (ρ i).elim 1 (hexOddCoordinatePolynomial (e j).val))).det

theorem eval_hexOddMinorPolynomial {r m n : ℕ} (a : HexOddVariable r m → ℝ)
    (f : Finset (HexVertex r)) (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)) :
    MvPolynomial.eval a (hexOddMinorPolynomial f e ρ) =
      (Matrix.of (fun i j => (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l))).det := by
  rw [hexOddMinorPolynomial, RingHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.eval a ((ρ i).elim 1 (hexOddCoordinatePolynomial (e j).val)) =
    (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l)
  cases hi : ρ i with
  | none => simp
  | some l => exact eval_hexOddCoordinatePolynomial a (e j).val l

/-- Oddness does not make any such minor polynomial identically zero. -/
theorem hexOddMinorPolynomial_ne_zero {r m n : ℕ} (f : Finset (HexVertex r))
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (e : Fin n ≃ f)
    (ρ : Fin n ↪ Option (Fin m)) : hexOddMinorPolynomial f e ρ ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_hexOddParameters_augmented_det_one f hf e ρ
  intro h
  have he := eval_hexOddMinorPolynomial a f e ρ
  rw [h, map_zero, ha] at he
  exact zero_ne_one he

/-- Any finite family of actual distinct-row minors can be made nonzero by a
nearby odd perturbation retaining zero-freeness. No polynomial nonvanishing
hypothesis is assumed: it follows from the absence of antipodal vertex pairs. -/
theorem exists_odd_zeroFree_minor_perturbation {r m : ℕ} {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (f : ι → Finset (HexVertex r))
    (hf : ∀ i v, v ∈ f i → hexVertexOpposite v ∉ f i)
    (e : ∀ i, Fin (n i) ≃ f i) (ρ : ∀ i, Fin (n i) ↪ Option (Fin m))
    (p : HexVertex r → Point m) (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hz : HexZeroFree p) (U : Set (HexVertex r → Point m)) (hU : IsOpen U) (hpu : p ∈ U) :
    ∃ a : HexOddVariable r m → ℝ,
      hexOddConfiguration a ∈ U ∧ HexZeroFree (hexOddConfiguration a) ∧
        ∀ i, (Matrix.of (fun j l => (ρ i j).elim 1
          (fun c => hexOddConfiguration a (e i l).val c))).det ≠ 0 := by
  obtain ⟨a, ha, hz', hne⟩ := exists_odd_zeroFree_polynomial_perturbation p hp hz
    (fun i => hexOddMinorPolynomial (f i) (e i) (ρ i))
    (fun i => hexOddMinorPolynomial_ne_zero (f i) (hf i) (e i) (ρ i)) U hU hpu
  exact ⟨a, ha, hz', fun i => by simpa only [eval_hexOddMinorPolynomial] using hne i⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonAllMinorsGeneric` -/


/-!
# A finite family containing every admissible odd-configuration minor

A square minor has at most m+1 rows: m coordinate rows and one mass row.
Index all such row selections, all vertex sets without antipodal pairs, and
all enumerations of those sets. Thus no choice of face ordering is omitted.
-/

namespace VCDimConvexBound

open scoped Matrix

/-- All square distinct-row minors on vertex sets without antipodal pairs. -/
def HexAllMinorsGeneric {r m : ℕ} (p : HexVertex r → Point m) : Prop :=
  ∀ (n : ℕ) (f : Finset (HexVertex r)),
    (∀ v ∈ f, hexVertexOpposite v ∉ f) →
    ∀ (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)),
      (Matrix.of (fun i j => (ρ i).elim 1 (fun l => p (e j).val l))).det ≠ 0

/-- The row bound makes the full collection of patterns a finite type. -/
abbrev HexMinorIndex (r m : ℕ) :=
  Σ n : Fin (m + 2),
    Σ f : {f : Finset (HexVertex r) // ∀ v ∈ f, hexVertexOpposite v ∉ f},
      (Fin n.val ≃ f.val) × (Fin n.val ↪ Option (Fin m))

/-- A row embedding has at most m+1 rows, including the optional mass row. -/
theorem hexMinor_row_bound {m n : ℕ} (ρ : Fin n ↪ Option (Fin m)) : n < m + 2 := by
  have h := Fintype.card_le_of_injective ρ ρ.injective
  simp only [Fintype.card_fin, Fintype.card_option] at h
  omega

/-- A nearby odd zero-free configuration satisfies every admissible minor
condition, including every enumeration and every row order. -/
theorem exists_odd_zeroFree_allMinors_perturbation {r m : ℕ}
    (p : HexVertex r → Point m) (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hz : HexZeroFree p) (U : Set (HexVertex r → Point m)) (hU : IsOpen U) (hpu : p ∈ U) :
    ∃ q : HexVertex r → Point m,
      q ∈ U ∧ (∀ v, q (hexVertexOpposite v) = -q v) ∧
        HexZeroFree q ∧ HexAllMinorsGeneric q := by
  classical
  let : Fintype (HexMinorIndex r m) := Fintype.ofFinite _
  obtain ⟨a, ha, hz', hne⟩ := exists_odd_zeroFree_minor_perturbation
    (fun i : HexMinorIndex r m => i.1.val)
    (fun i => i.2.1.val) (fun i => i.2.1.property)
    (fun i => i.2.2.1) (fun i => i.2.2.2) p hp hz U hU hpu
  refine ⟨hexOddConfiguration a, ha, hexOddConfiguration_odd a, hz', ?_⟩
  intro n f hf e ρ
  exact hne ⟨⟨n, hexMinor_row_bound ρ⟩, ⟨f, hf⟩, e, ρ⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonGenericTransport` -/


/-!
# Transport of all minors to the exact coordinate-flag conditions

Rows are represented by distinct optional coordinate indices. The optional
index none is the mass row. The height coordinate is outside the lower
coordinate prefix. These embeddings cover the six determinant patterns in
HexFlagGeneric, including the two successive column deletions.
-/

namespace VCDimConvexBound

open scoped Matrix

/-- Prepend a new value to an embedding of a finite index set. -/
def hexPrependRowEmbedding {α : Type*} {n : ℕ} (ρ : Fin n ↪ α)
    (a : α) (ha : ∀ i, a ≠ ρ i) : Fin (n + 1) ↪ α where
  toFun := Fin.cons a ρ
  inj' := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro h; exact (ha j h).elim
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro h; exact (ha i h.symm).elim
      · intro h
        exact congrArg Fin.succ (ρ.injective h)

/-- The lower coordinate prefix, in the order used by the flag matrices. -/
def hexFlagCoordinateRows {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    Fin k ↪ Option (Fin m) where
  toFun i := some ⟨i.rev.val, lt_of_lt_of_le i.rev.isLt hk⟩
  inj' := by
    intro i j h
    apply Fin.rev_injective
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.val) (Option.some.inj h)

/-- Prepend the constant mass row to the lower coordinate prefix. -/
def hexFlagMassRows {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    Fin (k + 1) ↪ Option (Fin m) :=
  hexPrependRowEmbedding (hexFlagCoordinateRows k hk) none (by
    intro i
    simp [hexFlagCoordinateRows])

/-- Prepend the next height row to the mass row and lower coordinates. -/
def hexFlagAugmentedRows {m : ℕ} (k : ℕ) (hk : k < m) :
    Fin (k + 2) ↪ Option (Fin m) :=
  hexPrependRowEmbedding (hexFlagMassRows k hk.le) (some ⟨k, hk⟩) (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change some (⟨k, hk⟩ : Fin m) ≠ none
      exact Option.some_ne_none _
    · intro h
      have hv : k = j.rev.val := congrArg Fin.val (Option.some.inj h)
      have hj := j.rev.isLt
      omega)

/-- Exclusion of antipodal pairs passes to a subset, including an empty one. -/
theorem hexNoAntipodal_subset {r : ℕ} {f g : Finset (HexVertex r)}
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (hg : g ⊆ f) :
    ∀ v ∈ g, hexVertexOpposite v ∉ g :=
  fun v hv hA => hf v (hg hv) (hg hA)

theorem hexFlagEnumMatrix_eq_coordinate_minor {r m n k : ℕ}
    (p : HexVertex r → Point m) (hk : k ≤ m)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) :
    hexFlagEnumMatrix (hexFlagExtend p) k e =
      Matrix.of (fun i j => (hexFlagCoordinateRows k hk i).elim 1
        (fun l => p (e j).val l)) := by
  ext i j
  have hi : i.rev.val < m := lt_of_lt_of_le i.rev.isLt hk
  change (if h : i.rev.val < m then p (e j).val ⟨i.rev.val, h⟩ else 0) = _
  rw [dite_eq_left hi]
  rfl

theorem hexFlagMassMatrix_eq_minor {r m n k : ℕ}
    (p : HexVertex r → Point m) (hk : k ≤ m)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) :
    flagPrependRow (fun _ => 1) (hexFlagEnumMatrix (hexFlagExtend p) k e) =
      Matrix.of (fun i j => (hexFlagMassRows k hk i).elim 1
        (fun l => p (e j).val l)) := by
  rw [hexFlagEnumMatrix_eq_coordinate_minor p hk]
  ext i j
  exact Fin.cases rfl (fun _ => rfl) i

theorem hexFlagAugmentedMatrix_eq_minor {r m n k : ℕ}
    (p : HexVertex r → Point m) (hk : k < m)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) :
    flagPrependRow (fun j => hexFlagExtend p (e j).val k)
      (flagPrependRow (fun _ => 1) (hexFlagEnumMatrix (hexFlagExtend p) k e)) =
      Matrix.of (fun i j => (hexFlagAugmentedRows k hk i).elim 1
        (fun l => p (e j).val l)) := by
  rw [hexFlagMassMatrix_eq_minor p hk.le]
  ext i j
  refine Fin.cases ?_ (fun _ => rfl) i
  change hexFlagExtend p (e j).val k = p (e j).val ⟨k, hk⟩
  simp only [hexFlagExtend, dite_eq_left hk]

/-- Row prepending commutes with arbitrary column selection. -/
theorem flagPrependRow_submatrix {k n l : ℕ} (z : Fin n → ℝ)
    (X : Matrix (Fin k) (Fin n) ℝ) (c : Fin l → Fin n) :
    (flagPrependRow z X).submatrix id c =
      flagPrependRow (fun j => z (c j)) (X.submatrix id c) := by
  ext i j
  exact Fin.cases rfl (fun _ => rfl) i

/-- Coordinate-only square matrices are among the admissible minors. -/
theorem HexAllMinorsGeneric.coordinate {r m k : ℕ} {p : HexVertex r → Point m}
    (hG : HexAllMinorsGeneric p) (hk : k ≤ m)
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin k ≃ f) : (hexFlagEnumMatrix (hexFlagExtend p) k e).det ≠ 0 := by
  rw [hexFlagEnumMatrix_eq_coordinate_minor p hk]
  exact hG k f hf e (hexFlagCoordinateRows k hk)

/-- Mass-augmented square matrices are among the admissible minors. -/
theorem HexAllMinorsGeneric.mass {r m k : ℕ} {p : HexVertex r → Point m}
    (hG : HexAllMinorsGeneric p) (hk : k ≤ m)
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin (k + 1) ≃ f) :
    (flagPrependRow (fun _ => 1) (hexFlagEnumMatrix (hexFlagExtend p) k e)).det ≠ 0 := by
  rw [hexFlagMassMatrix_eq_minor p hk]
  exact hG (k + 1) f hf e (hexFlagMassRows k hk)

/-- Height-augmented square matrices are the next coordinate prefix. -/
theorem HexAllMinorsGeneric.height {r m k : ℕ} {p : HexVertex r → Point m}
    (hG : HexAllMinorsGeneric p) (hk : k < m)
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin (k + 1) ≃ f) :
    (flagPrependRow (fun j => hexFlagExtend p (e j).val k)
      (hexFlagEnumMatrix (hexFlagExtend p) k e)).det ≠ 0 := by
  rw [← hexFlagEnumMatrix_succ]
  exact hG.coordinate hk f hf e

/-- All four determinant hypotheses of a boundary slice follow from all minors. -/
theorem HexAllMinorsGeneric.slice {r m k : ℕ} {p : HexVertex r → Point m}
    (hG : HexAllMinorsGeneric p) (hk : k < m)
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin (k + 2) ≃ f) :
    FlagSliceGeneric (hexFlagEnumMatrix (hexFlagExtend p) k e)
      (fun j => hexFlagExtend p (e j).val k) := by
  have he (i : Fin (k + 2)) := hexNoAntipodal_subset hf (Finset.erase_subset (e i).val f)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [sliceDeleteColumn, flagConstraintMatrix, flagPrependRow_submatrix]
    exact hG.mass hk.le _ (he i) (hexFaceEraseEnumeration e i)
  · intro i j
    exact hG.coordinate hk.le _
      (hexNoAntipodal_subset (he i) (Finset.erase_subset _ _))
      (hexFaceEraseEnumeration (hexFaceEraseEnumeration e i) j)
  · rw [flagConstraintMatrix, hexFlagAugmentedMatrix_eq_minor p hk]
    exact hG (k + 2) f hf e (hexFlagAugmentedRows k hk)
  · intro i
    rw [sliceDeleteColumn, flagPrependRow_submatrix]
    exact hG.height hk _ (he i) (hexFaceEraseEnumeration e i)

/-- The full finite minor family supplies exactly the existing flag structure. -/
theorem HexAllMinorsGeneric.flag {r : ℕ} {p : HexVertex r → Point (2 * r - 1)}
    (hG : HexAllMinorsGeneric p) : HexFlagGeneric (hexFlagExtend p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk f hf e
    exact hG.slice (by omega) f (hexFace_no_antipodal f hf) e
  · intro k hk f hf e
    exact hG.mass (by omega) f (hexFace_no_antipodal f hf) e
  · intro k hk f hf e
    exact hG.height (by omega) f (hexFace_no_antipodal f hf) e

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonOddZero` -/


/-!
# A barycentric zero for every odd vertex configuration

All determinant conditions are removed. If no facet had a zero, openness
would preserve that property under a small odd perturbation. The finite
minor family supplies a generic perturbation, contradicting the already
proved generic odd zero theorem.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Supply exactly HexFlagGeneric by an odd perturbation inside any specified
open neighborhood, retaining zero-freeness if it held initially. -/
theorem exists_odd_zeroFree_flagGeneric_perturbation {r : ℕ}
    (p : HexVertex r → Point (2 * r - 1))
    (hp : ∀ v, p (hexVertexOpposite v) = -p v) (hz : HexZeroFree p)
    (U : Set (HexVertex r → Point (2 * r - 1))) (hU : IsOpen U) (hpu : p ∈ U) :
    ∃ q : HexVertex r → Point (2 * r - 1),
      q ∈ U ∧ (∀ v, q (hexVertexOpposite v) = -q v) ∧
        HexZeroFree q ∧ HexFlagGeneric (hexFlagExtend q) := by
  obtain ⟨q, hq, hodd, hz', hG⟩ :=
    exists_odd_zeroFree_allMinors_perturbation p hp hz U hU hpu
  exact ⟨q, hq, hodd, hz', hG.flag⟩

/-- Every odd vertex configuration in dimension 2r-1 has a barycentric zero
on an actual maximal face. No general-position hypothesis remains. -/
theorem hexOdd_exists_barycentric_zero {r : ℕ} (hr : 0 < r)
    (p : HexVertex r → Point (2 * r - 1))
    (hp : ∀ v, p (hexVertexOpposite v) = -p v) :
    ∃ s : Fin r → Fin 6, ∃ x : (hexFacet s) → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v • p v.val) = 0 := by
  apply (not_hexZeroFree_iff_barycentric_zero p).mp
  intro hz
  obtain ⟨q, _, hodd, hz', hG⟩ :=
    exists_odd_zeroFree_flagGeneric_perturbation p hp hz Set.univ isOpen_univ (Set.mem_univ p)
  exact not_hexZeroFree_of_generic_odd hr q hodd hG hz'

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonRealization` -/


/-!
# Realizing the hexagon-join facets in the actual input space

Nonnegative parameters of mass one are the barycentric weights of the
2r vertices of the corresponding abstract facet. Thus the finite domain
used for the boundary calculation is connected to the original hexagon map.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Place one hexagon ray in the indicated color plane. -/
def hexDomainVertex {r : ℕ} (v : HexVertex r) : HexagonDomain r :=
  fun k => if k = v.1 then hexSectorMap v.2 (1, 0) else 0

/-- The sector parameters, indexed by the two vertices in each color. -/
def hexFacetWeight {r : ℕ} (t : HexagonDomain r) (e : Fin r × Bool) : ℝ :=
  if e.2 then (t e.1).2 else (t e.1).1

theorem hexFacetWeight_nonneg {r : ℕ} (t : HexagonDomain r) (ht : HexNonnegative t)
    (e : Fin r × Bool) : 0 ≤ hexFacetWeight t e := by
  rcases e with ⟨k, b⟩
  cases b
  · exact (ht k).1
  · exact (ht k).2

theorem sum_hexFacetWeight {r : ℕ} (t : HexagonDomain r) :
    (∑ e : Fin r × Bool, hexFacetWeight t e) = hexParameterMass t := by
  simp [hexFacetWeight, Fintype.sum_prod_type, hexParameterMass, add_comm]

/-- The two ray generators recover the linear sector parameterization. -/
theorem hexSectorMap_eq_ray_combination (s : Fin 6) (t : ℝ × ℝ) :
    hexSectorMap s t = t.1 • hexSectorMap s (1, 0) +
      t.2 • hexSectorMap (hexNext s) (1, 0) := by
  fin_cases s <;> ext <;> simp [hexSectorMap, hexNext] <;> ring

/-- The actual point is the weighted sum of the vertices of the abstract facet. -/
theorem hexSectorArray_eq_facet_combination {r : ℕ} (s : Fin r → Fin 6)
    (t : HexagonDomain r) :
    hexSectorArray s t = ∑ e : Fin r × Bool,
      hexFacetWeight t e • hexDomainVertex (hexFacetVertex s e) := by
  funext k
  change hexSectorMap (s k) (t k) = _
  rw [hexSectorMap_eq_ray_combination]
  simp [hexFacetWeight, hexDomainVertex, hexFacetVertex, Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]

/-- Every normalized nonnegative sector point has actual barycentric coordinates. -/
theorem hexSectorArray_normalized_barycentric {r : ℕ} (s : Fin r → Fin 6)
    (t : HexagonDomain r) (ht : HexNonnegative t) (hm : hexParameterMass t = 1) :
    (∀ e, 0 ≤ hexFacetWeight t e) ∧ (∑ e, hexFacetWeight t e) = 1 ∧
      hexSectorArray s t = ∑ e, hexFacetWeight t e • hexDomainVertex (hexFacetVertex s e) :=
  ⟨hexFacetWeight_nonneg t ht, (sum_hexFacetWeight t).trans hm,
    hexSectorArray_eq_facet_combination s t⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonVertexBridge` -/


/-!
# Barycentric facet zeros give the actual normalized cone certificate

The two coordinate unit vectors in each color map to the actual vertices
of the selected hexagon facet. The concrete map is linear on that sector,
so its value is the corresponding weighted sum of vertex images.
-/

namespace VCDimConvexBound

open scoped BigOperators

theorem hexDomainVertex_opposite {r : ℕ} (v : HexVertex r) :
    hexDomainVertex (hexVertexOpposite v) = -hexDomainVertex v := by
  funext k
  simp only [hexDomainVertex, hexVertexOpposite, Pi.neg_apply]
  by_cases h : k = v.1
  · simp [h, hexSectorMap_opposite]
  · simp [h]

/-- The two endpoints per color enumerate the actual facet without repetition. -/
noncomputable def hexFacetVertexEquiv {r : ℕ} (s : Fin r → Fin 6) :
    (Fin r × Bool) ≃ hexFacet s :=
  Equiv.ofBijective (fun e => ⟨hexFacetVertex s e, hexFacetVertex_mem s e⟩) (by
    constructor
    · intro i j h
      exact hexFacetVertex_injective s (congrArg Subtype.val h)
    · rintro ⟨v, hv⟩
      obtain ⟨e, _, he⟩ := Finset.mem_image.mp hv
      exact ⟨e, Subtype.ext he⟩)

/-- A unit vector in one of the two nonnegative coordinates of one color. -/
def hexParameterVertex {r : ℕ} (e : Fin r × Bool) : HexagonDomain r :=
  fun k => if k = e.1 then (if e.2 then (0, 1) else (1, 0)) else 0

theorem hexParameterVertex_nonnegative {r : ℕ} (e : Fin r × Bool) :
    HexNonnegative (hexParameterVertex e) := by
  intro k
  rcases e with ⟨l, b⟩
  cases b <;> by_cases h : k = l <;> simp [hexParameterVertex, h]

theorem hexSectorArray_parameterVertex {r : ℕ} (s : Fin r → Fin 6)
    (e : Fin r × Bool) :
    hexSectorArray s (hexParameterVertex e) = hexDomainVertex (hexFacetVertex s e) := by
  rcases e with ⟨l, b⟩
  funext k
  by_cases h : k = l
  · subst k
    cases b
    · simp [hexSectorArray, hexParameterVertex, hexDomainVertex, hexFacetVertex]
    · have he := hexSectorMap_eq_ray_combination (s l) (0, 1)
      simpa [hexSectorArray, hexParameterVertex, hexDomainVertex, hexFacetVertex] using he
  · simp [hexSectorArray, hexParameterVertex, hexDomainVertex, hexFacetVertex, h]

/-- The actual vertex images are evaluations of the same linear piece. -/
theorem hexPieceLinear_parameterVertex {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (e : Fin r × Bool) :
    hexPieceLinear z s (hexParameterVertex e) =
      hexagonCayleyMap z (hexDomainVertex (hexFacetVertex s e)) := by
  rw [← hexagonCayleyMap_sector z s _ (hexParameterVertex_nonnegative e),
    hexSectorArray_parameterVertex]

/-- The parameter vector associated to arbitrary endpoint weights. -/
def hexParametersOfWeights {r : ℕ} (w : Fin r × Bool → ℝ) : HexagonDomain r :=
  fun k => (w (k, false), w (k, true))

theorem hexParametersOfWeights_eq_sum {r : ℕ} (w : Fin r × Bool → ℝ) :
    hexParametersOfWeights w = ∑ e, w e • hexParameterVertex e := by
  funext k
  apply Prod.ext <;>
    simp [hexParametersOfWeights, hexParameterVertex, Finset.sum_apply,
      Fintype.sum_prod_type]

theorem hexParameterMass_ofWeights {r : ℕ} (w : Fin r × Bool → ℝ) :
    hexParameterMass (hexParametersOfWeights w) = ∑ e, w e := by
  simp [hexParameterMass, hexParametersOfWeights, Fintype.sum_prod_type, add_comm]

/-- On a selected facet, the concrete nonlinear formula has the expected
linear interpolation of its actual vertex images. -/
theorem hexPieceLinear_ofWeights {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (w : Fin r × Bool → ℝ) :
    hexPieceLinear z s (hexParametersOfWeights w) =
      ∑ e, w e • hexagonCayleyMap z (hexDomainVertex (hexFacetVertex s e)) := by
  rw [hexParametersOfWeights_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_smul, hexPieceLinear_parameterVertex]

/-- A barycentric zero of the actual facet vertex images is the required
nonnegative mass-one kernel vector of its concrete linear piece. -/
theorem exists_hexPiece_kernel_of_facet_zero {r D : ℕ}
    (z : Fin r → Fin 3 → Point D) (s : Fin r → Fin 6)
    (x : (hexFacet s) → ℝ) (hm : ∑ v, x v = 1) (hx : ∀ v, 0 ≤ x v)
    (hz : ∑ v, x v • hexagonCayleyMap z (hexDomainVertex v.val) = 0) :
    ∃ t : HexagonDomain r,
      HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0 := by
  let w : Fin r × Bool → ℝ := fun e => x (hexFacetVertexEquiv s e)
  refine ⟨hexParametersOfWeights w, ?_, ?_, ?_⟩
  · intro k
    exact ⟨hx _, hx _⟩
  · rw [hexParameterMass_ofWeights]
    exact ((hexFacetVertexEquiv s).sum_comp x).trans hm
  · rw [hexPieceLinear_ofWeights]
    exact ((hexFacetVertexEquiv s).sum_comp
      (fun v => x v • hexagonCayleyMap z (hexDomainVertex v.val))).trans hz

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HypersurfaceSigns` -/


/-!
# From a coarse hypersurface component bound to polynomial sign counts

The component estimate is an explicit, unproved input. The reductions here
are proved: nonzero continuous functions keep their signs on a component,
and adjoining the inverse of a product realizes its nonzero locus inside
a single polynomial zero set. No Warren bound is assumed.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The zero set carries its induced topology, including empty and singular cases. -/
abbrev PolynomialZeroSet {σ : Type*} (f : MvPolynomial σ ℝ) :=
  {x : σ → ℝ // MvPolynomial.eval x f = 0}

/-- The remaining coarse Milnor-type input. Finiteness is stated explicitly,
since `Nat.card` alone would assign zero to an infinite component type.
Only connected components, not higher homology, occur in this obligation. -/
def HypersurfaceComponentBound : Prop :=
  ∀ (σ : Type) [Fintype σ] (k : ℕ), 0 < k →
    ∀ f : MvPolynomial σ ℝ, f.totalDegree ≤ k →
      Finite (ConnectedComponents (PolynomialZeroSet f)) ∧
      Nat.card (ConnectedComponents (PolynomialZeroSet f)) ≤ (2 * k) ^ Fintype.card σ

/-- A nonvanishing real continuous function has the same sign throughout a component. -/
theorem pos_iff_of_connectedComponents_eq {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (hn : ∀ x, f x ≠ 0)
    {x y : X} (hxy : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    (0 < f x ↔ 0 < f y) := by
  have hc : connectedComponent x = connectedComponent y :=
    ConnectedComponents.coe_eq_coe.mp hxy
  have hy : y ∈ connectedComponent x := hc ▸ mem_connectedComponent
  have same {a b : X} (ha : a ∈ connectedComponent x) (hb : b ∈ connectedComponent x)
      (hpos : 0 < f a) : 0 < f b := by
    by_contra h
    obtain ⟨z, _, hz⟩ := isPreconnected_connectedComponent.intermediate_value hb ha
      hf.continuousOn (show 0 ∈ Set.Icc (f b) (f a) from ⟨le_of_not_gt h, hpos.le⟩)
    exact hn z hz
  exact ⟨same mem_connectedComponent hy, same hy mem_connectedComponent⟩

/-- Select one witnessing point per strict word. Distinct words give distinct components. -/
theorem card_strictPatterns_le_components {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] [Finite (ConnectedComponents X)]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (hn : ∀ i x, f i x ≠ 0) :
    (strictPatterns f).card ≤ Nat.card (ConnectedComponents X) := by
  classical
  have hw (s : strictPatterns f) : ∃ x, ∀ i, if s.val i then 0 < f i x else f i x < 0 := by
    simpa [strictPatterns] using s.property
  choose x hx using hw
  have hinj : Function.Injective (fun s : strictPatterns f => ConnectedComponents.mk (x s)) := by
    intro s t h
    apply Subtype.ext
    funext i
    have hp := pos_iff_of_connectedComponents_eq (f i) (hf i) (hn i) h
    have hs := hx s i
    have ht := hx t i
    cases hs' : s.val i <;> cases ht' : t.val i <;> simp_all <;> linarith
  simpa using Nat.card_le_card_of_injective _ hinj

/-- The equation `u * product(f_i) - 1 = 0`, with `none` indexing u. -/
noncomputable def inverseProductPolynomial {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℝ) : MvPolynomial (Option σ) ℝ :=
  MvPolynomial.X none * MvPolynomial.rename some (∏ i, f i) - 1

theorem eval_inverseProductPolynomial {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℝ) (x : Option σ → ℝ) :
    MvPolynomial.eval x (inverseProductPolynomial f) =
      x none * (∏ i, MvPolynomial.eval (fun j => x (some j)) (f i)) - 1 := by
  simp [inverseProductPolynomial, MvPolynomial.eval_rename, Function.comp_def]

/-- The extra inverse variable adds one to the sum of the degrees. -/
theorem totalDegree_inverseProductPolynomial_le {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℝ) (k : ℕ) (hf : ∀ i, (f i).totalDegree ≤ k) :
    (inverseProductPolynomial f).totalDegree ≤ k * Fintype.card ι + 1 := by
  have hprod : (∏ i, f i).totalDegree ≤ k * Fintype.card ι := by
    calc
      _ ≤ ∑ i, (f i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ _i : ι, k := Finset.sum_le_sum (fun i _ => hf i)
      _ = _ := by simp [Nat.mul_comm]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa [Nat.add_comm] using Nat.add_le_add_left
        ((MvPolynomial.totalDegree_rename_le some _).trans hprod) 1)
  · simp

/-- Every factor is nonzero at every point of the inverse-product hypersurface. -/
theorem eval_ne_zero_on_inverseProduct {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℝ) (x : PolynomialZeroSet (inverseProductPolynomial f))
    (i : ι) : MvPolynomial.eval (fun j => x.val (some j)) (f i) ≠ 0 := by
  have h := x.property
  rw [eval_inverseProductPolynomial, sub_eq_zero] at h
  have hp : (∏ j, MvPolynomial.eval (fun a => x.val (some a)) (f j)) ≠ 0 := by
    intro hz
    simp [hz] at h
  exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)

/-- Restricting to the inverse-product hypersurface preserves exactly the strict words. -/
theorem strictPatterns_inverseProduct {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℝ) :
    strictPatterns (fun i (x : PolynomialZeroSet (inverseProductPolynomial f)) =>
      MvPolynomial.eval (fun j => x.val (some j)) (f i)) =
    strictPatterns (fun i x => MvPolynomial.eval x (f i)) := by
  classical
  ext s
  simp only [strictPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun j => x.val (some j), hx⟩
  · rintro ⟨x, hx⟩
    have hne (i : ι) : MvPolynomial.eval x (f i) ≠ 0 := by
      have h := hx i
      cases hs : s i <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at h
      · exact ne_of_lt h
      · exact ne_of_gt h
    have hp : (∏ i, MvPolynomial.eval x (f i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)
    let y : Option σ → ℝ := fun o => o.elim (∏ i, MvPolynomial.eval x (f i))⁻¹ x
    have hy : MvPolynomial.eval y (inverseProductPolynomial f) = 0 := by
      rw [eval_inverseProductPolynomial]
      change (∏ i, MvPolynomial.eval x (f i))⁻¹ * (∏ i, MvPolynomial.eval x (f i)) - 1 = 0
      rw [inv_mul_cancel₀ hp, sub_self]
    exact ⟨⟨y, hy⟩, hx⟩

/-- A single hypersurface estimate suffices for a coarse strict sign count. -/
theorem card_strictPatterns_le_of_hypersurface {ι : Type*} {σ : Type}
    [Fintype ι] [Fintype σ] (hM : HypersurfaceComponentBound)
    (k : ℕ) (f : ι → MvPolynomial σ ℝ) (hf : ∀ i, (f i).totalDegree ≤ k) :
    (strictPatterns (fun i x => MvPolynomial.eval x (f i))).card ≤
      (2 * k * Fintype.card ι + 2) ^ (Fintype.card σ + 1) := by
  obtain ⟨hfin, hcard⟩ := hM (Option σ) (k * Fintype.card ι + 1) (by omega)
    (inverseProductPolynomial f) (totalDegree_inverseProductPolynomial_le f k hf)
  let := hfin
  rw [← strictPatterns_inverseProduct f]
  refine (card_strictPatterns_le_components _ (fun i => ?_)
    (fun i x => eval_ne_zero_on_inverseProduct f x i)).trans (hcard.trans_eq ?_)
  · exact (MvPolynomial.continuous_eval (f i)).comp
      (continuous_pi fun j => (continuous_apply (some j)).comp continuous_subtype_val)
  · simp only [Fintype.card_option]
    congr 1
    ring

/-- Ternary signs cost one perturbation variable and twice as many factors.
No lower bound on the number of polynomials is needed. -/
theorem card_ternaryPatterns_le_of_hypersurface {ι : Type*} {σ : Type}
    [Fintype ι] [Fintype σ] (hM : HypersurfaceComponentBound)
    (k : ℕ) (hk : 1 ≤ k) (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ k) :
    (ternaryPatterns (fun i x => MvPolynomial.eval x (f i))).card ≤
      (4 * k * Fintype.card ι + 2) ^ (Fintype.card σ + 2) := by
  have h := card_strictPatterns_le_of_hypersurface hM k (perturbPolynomials f)
    (totalDegree_perturbPolynomials_le f k hk hf)
  have hc := card_ternaryPatterns_le_strictPatterns_perturb
    (fun i x => MvPolynomial.eval x (f i))
  rw [← card_strictPatterns_perturbPolynomials f] at hc
  refine hc.trans (h.trans_eq ?_)
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
  congr 1
  ring

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.Minors` -/


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


/-! ## Source module `VCDimConvexBound.MinorSignPatterns` -/


/-!
# Counting all-minor sign patterns, conditional on Warren

This connects the polynomial encoding of additive arrays with the proved
ternary-to-strict reduction. The geometric assertion that minor signs determine
convex-hull membership is proved separately in `MinorHullRecovery`.
Warren itself is still unproved.
-/

namespace VCDimConvexBound

/-- All ternary sign vectors of the polynomial minor family. -/
noncomputable def minorSignPatterns (D m : ℕ) : Finset (MinorIndex D m → Fin 3) :=
  ternaryPatterns (fun j x => MvPolynomial.eval x (minorPolynomial j))

/-- Substitute the minor degree, number of variables, and index-count bound into Warren. -/
theorem card_minorSignPatterns_le_of_warren (hW : WarrenStrictBound)
    (D m : ℕ) (hD : 2 ≤ D) (hm : D ^ 2 ≤ m) :
    ((minorSignPatterns D m).card : ℝ) ≤
      (8 * Real.exp 1 * D * (2 ^ (D + 1) * ((m : ℝ) ^ D) ^ (D + 1)) /
        (D ^ 2 * m + 1)) ^ (D ^ 2 * m + 1) := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have h := card_ternaryPatterns_le_of_warren hW D (by omega)
    (show Fintype.card (ArrayVar D m) + 1 ≤ 2 * Fintype.card (MinorIndex D m) by
      rw [card_arrayVar]
      exact minor_warren_size_condition D m hD hm)
    (minorPolynomial (D := D) (m := m)) totalDegree_minorPolynomial_le
  simp only [card_arrayVar] at h
  change ((minorSignPatterns D m).card : ℝ) ≤ _ at h
  have hcount : (Fintype.card (MinorIndex D m) : ℝ) ≤
      2 ^ (D + 1) * ((m : ℝ) ^ D) ^ (D + 1) := by
    exact_mod_cast card_minorIndex_le D m hm0
  push_cast at h
  exact h.trans (by gcongr)

/-- The side length already chosen in P3 meets the elementary Warren size condition. -/
theorem sq_le_explicit_side (D : ℕ) (hD : 2 ≤ D) :
    D ^ 2 ≤ 2 ^ (8 * (D + 1) ^ (D - 1)) := by
  have hbase : D ≤ 2 ^ D := (Nat.lt_two_pow_self (n := D)).le
  have hexp : D + 1 ≤ (D + 1) ^ (D - 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < D + 1) (by omega : 1 ≤ D - 1)
  calc
    D ^ 2 ≤ (2 ^ D) ^ 2 := by gcongr
    _ = 2 ^ (D * 2) := (pow_mul 2 D 2).symm
    _ ≤ 2 ^ (8 * (D + 1) ^ (D - 1)) :=
      Nat.pow_le_pow_right (by decide) (by omega)

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SignCountConstants` -/


/-!
# Elementary power bounds for the minor sign count

We deliberately overestimate the Warren expression, retaining the original
side length m = 2^(8(D+1)^(D-1)). No logarithms or giant enumerations are needed.
-/

namespace VCDimConvexBound

/-- The elementary exponential budget behind the sign count. -/
theorem explicit_sign_exponent_budget (D : ℕ) (hD : 2 ≤ D) :
    8 * (8 * (D + 1) ^ (D - 1)) * (D + 1) ^ 4 <
      2 ^ (8 * (D + 1) ^ (D - 1)) := by
  let s := (D + 1) ^ (D - 1)
  have hDs : D + 1 ≤ s := by
    simpa [s] using Nat.pow_le_pow_right (by omega : 0 < D + 1) (by omega : 1 ≤ D - 1)
  have hs : 3 ≤ s := by omega
  have hs2 : s ≤ 2 ^ s := (Nat.lt_two_pow_self (n := s)).le
  calc
    8 * (8 * s) * (D + 1) ^ 4 ≤ 64 * s ^ 5 := by
      calc
        _ ≤ 8 * (8 * s) * s ^ 4 := by gcongr
        _ = _ := by ring
    _ ≤ 64 * (2 ^ s) ^ 5 := by gcongr
    _ = 2 ^ (6 + 5 * s) := by
      rw [pow_add, ← pow_mul, Nat.mul_comm s 5]
      norm_num
    _ < 2 ^ (8 * s) := Nat.pow_lt_pow_right (by decide) (by omega)

/-- Replace the real Warren base by a convenient power of two. -/
theorem minor_warren_base_le_two_pow (D L : ℕ) (hL : 8 ≤ L) :
    8 * Real.exp 1 * D * (2 ^ (D + 1) * (((2 ^ L : ℕ) : ℝ) ^ D) ^ (D + 1)) /
      (D ^ 2 * (2 ^ L : ℕ) + 1) ≤ (2 : ℝ) ^ (2 * L * (D + 1) ^ 2) := by
  have hD2 : (D : ℝ) ≤ (2 : ℝ) ^ D := by
    exact_mod_cast (Nat.lt_two_pow_self (n := D)).le
  have he : Real.exp 1 ≤ (4 : ℝ) := Real.exp_one_lt_three.le.trans (by norm_num)
  have hexp : 6 + 2 * D + L * D * (D + 1) ≤ 2 * L * (D + 1) ^ 2 := by
    nlinarith
  calc
    _ ≤ 8 * Real.exp 1 * D *
        (2 ^ (D + 1) * (((2 ^ L : ℕ) : ℝ) ^ D) ^ (D + 1)) :=
      div_le_self (by positivity) (le_add_of_nonneg_left (by positivity))
    _ ≤ 8 * 4 * (2 : ℝ) ^ D *
        (2 ^ (D + 1) * (((2 ^ L : ℕ) : ℝ) ^ D) ^ (D + 1)) := by gcongr
    _ = (2 : ℝ) ^ (6 + 2 * D + L * D * (D + 1)) := by
      push_cast
      rw [show 8 * (4 : ℝ) = 2 ^ 5 by norm_num]
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp

/-- A natural exponent upper bound for the sign-pattern count, conditional on Warren. -/
theorem card_minorSignPatterns_le_two_pow_of_warren (hW : WarrenStrictBound)
    (D L : ℕ) (hD : 2 ≤ D) (hL : 8 ≤ L) (hm : D ^ 2 ≤ 2 ^ L) :
    (minorSignPatterns D (2 ^ L)).card ≤ 2 ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
  have hw := card_minorSignPatterns_le_of_warren hW D (2 ^ L) hD hm
  have hb := minor_warren_base_le_two_pow D L hL
  have hp : D ^ 2 * 2 ^ L + 1 ≤ 2 * (D + 1) ^ 2 * 2 ^ L := by
    have hm0 : 0 < (2 : ℕ) ^ L := by positivity
    nlinarith [Nat.pow_le_pow_left (show D ≤ D + 1 by omega) 2]
  have hexp : (2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 1) ≤
      4 * L * (D + 1) ^ 4 * 2 ^ L := by
    calc
      _ ≤ (2 * L * (D + 1) ^ 2) * (2 * (D + 1) ^ 2 * 2 ^ L) := by gcongr
      _ = _ := by ring
  have hr : ((minorSignPatterns D (2 ^ L)).card : ℝ) ≤
      (2 : ℝ) ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
    calc
      _ ≤ _ := hw
      _ ≤ ((2 : ℝ) ^ (2 * L * (D + 1) ^ 2)) ^ (D ^ 2 * 2 ^ L + 1) := by
        gcongr
      _ = (2 : ℝ) ^ ((2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 1)) :=
        (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp
  exact_mod_cast hr

/-- P7: the sign factor uses strictly less than half the bit budget. -/
theorem card_minorSignPatterns_explicit_sq_lt_of_warren (hW : WarrenStrictBound)
    (D : ℕ) (hD : 2 ≤ D) :
    (minorSignPatterns D (2 ^ (8 * (D + 1) ^ (D - 1)))).card ^ 2 <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  let L := 8 * (D + 1) ^ (D - 1)
  let m := 2 ^ L
  have hL : 8 ≤ L := by
    have h : 0 < (D + 1) ^ (D - 1) := by positivity
    dsimp [L]; omega
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hb : 8 * L * (D + 1) ^ 4 < m := explicit_sign_exponent_budget D hD
  have hmD : m ^ 2 ≤ m ^ D := Nat.pow_le_pow_right hm0 hD
  have hexp : (4 * L * (D + 1) ^ 4 * m) * 2 < m ^ D := by
    calc
      _ = (8 * L * (D + 1) ^ 4) * m := by ring
      _ < m * m := Nat.mul_lt_mul_of_pos_right hb hm0
      _ ≤ m ^ D := by simpa [pow_two] using hmD
  have ht := card_minorSignPatterns_le_two_pow_of_warren hW D L hD hL
    (sq_le_explicit_side D hD)
  calc
    _ ≤ (2 ^ (4 * L * (D + 1) ^ 4 * m)) ^ 2 := Nat.pow_le_pow_left ht 2
    _ = 2 ^ ((4 * L * (D + 1) ^ 4 * m) * 2) := (pow_mul _ _ _).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) hexp

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.CoarseSignCount` -/


/-!
# The original sign-count budget from a coarse component bound

The bound `(4 D N + 2)^(D^2 m + 2)` is enough at the original side length.
All estimates are in natural numbers. The only unproved input is the
explicit `HypersurfaceComponentBound`, rather than Warren's sharper theorem.
-/

namespace VCDimConvexBound

/-- Apply the coarse estimate to all augmented minors, including degenerate ones. -/
theorem card_minorSignPatterns_le_of_hypersurface (hM : HypersurfaceComponentBound)
    (D m : ℕ) (hD : 1 ≤ D) (hm : 0 < m) :
    (minorSignPatterns D m).card ≤
      (4 * D * (2 ^ (D + 1) * (m ^ D) ^ (D + 1)) + 2) ^ (D ^ 2 * m + 2) := by
  have h := card_ternaryPatterns_le_of_hypersurface hM D hD
    (minorPolynomial (D := D) (m := m)) totalDegree_minorPolynomial_le
  simp only [card_arrayVar] at h
  change (minorSignPatterns D m).card ≤ _ at h
  exact h.trans (by gcongr; exact card_minorIndex_le D m hm)

/-- The coarse Milnor base fits inside the same power of two as the Warren base. -/
theorem minor_hypersurface_base_le_two_pow (D L : ℕ) (hD : 1 ≤ D) (hL : 8 ≤ L) :
    4 * D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) + 2 ≤
      2 ^ (2 * L * (D + 1) ^ 2) := by
  have hpos : 0 < D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by positivity
  have hexp : 4 + 2 * D + L * D * (D + 1) ≤ 2 * L * (D + 1) ^ 2 := by
    nlinarith
  calc
    _ ≤ 8 * D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by nlinarith
    _ ≤ 8 * (2 ^ D) * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by
      gcongr
      exact (Nat.lt_two_pow_self (n := D)).le
    _ = 2 ^ (4 + 2 * D + L * D * (D + 1)) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

/-- The extra two variables still fit inside the existing exponent budget. -/
theorem card_minorSignPatterns_le_two_pow_of_hypersurface (hM : HypersurfaceComponentBound)
    (D L : ℕ) (hD : 1 ≤ D) (hL : 8 ≤ L) :
    (minorSignPatterns D (2 ^ L)).card ≤ 2 ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
  have hm : 0 < (2 : ℕ) ^ L := by positivity
  have hp : D ^ 2 * 2 ^ L + 2 ≤ 2 * (D + 1) ^ 2 * 2 ^ L := by
    calc
      _ ≤ (D ^ 2 + 2) * 2 ^ L := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith : D ^ 2 + 2 ≤ 2 * (D + 1) ^ 2)
  have he : (2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2) ≤
      4 * L * (D + 1) ^ 4 * 2 ^ L := by
    calc
      _ ≤ (2 * L * (D + 1) ^ 2) * (2 * (D + 1) ^ 2 * 2 ^ L) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ _ := card_minorSignPatterns_le_of_hypersurface hM D (2 ^ L) hD hm
    _ ≤ (2 ^ (2 * L * (D + 1) ^ 2)) ^ (D ^ 2 * 2 ^ L + 2) :=
      Nat.pow_le_pow_left (minor_hypersurface_base_le_two_pow D L hD hL) _
    _ = 2 ^ ((2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

/-- The original explicit side length leaves strictly more than half the bit budget. -/
theorem card_minorSignPatterns_explicit_sq_lt_of_hypersurface
    (hM : HypersurfaceComponentBound) (D : ℕ) (hD : 2 ≤ D) :
    (minorSignPatterns D (2 ^ (8 * (D + 1) ^ (D - 1)))).card ^ 2 <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  let L := 8 * (D + 1) ^ (D - 1)
  let m := 2 ^ L
  have hL : 8 ≤ L := by
    have h : 0 < (D + 1) ^ (D - 1) := by positivity
    dsimp [L]
    omega
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hb : 8 * L * (D + 1) ^ 4 < m := explicit_sign_exponent_budget D hD
  have hmD : m ^ 2 ≤ m ^ D := Nat.pow_le_pow_right hm0 hD
  have he : (4 * L * (D + 1) ^ 4 * m) * 2 < m ^ D := by
    calc
      _ = (8 * L * (D + 1) ^ 4) * m := by ring
      _ < m * m := Nat.mul_lt_mul_of_pos_right hb hm0
      _ ≤ m ^ D := by simpa [pow_two] using hmD
  have ht := card_minorSignPatterns_le_two_pow_of_hypersurface hM D L (by omega) hL
  calc
    _ ≤ (2 ^ (4 * L * (D + 1) ^ 4 * m)) ^ 2 := Nat.pow_le_pow_left ht 2
    _ = 2 ^ ((4 * L * (D + 1) ^ 4 * m) * 2) := (pow_mul _ _ _).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) he

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.CramerSigns` -/


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
      simp_all only [signCode] <;> norm_num at *

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


/-! ## Source module `VCDimConvexBound.MinorIndependence` -/


/-!
# What all minor signs remember about linear systems

Independent columns admit a nonsingular row restriction. Equal signs for all
row-subset minors therefore preserve independence and membership in the span
of any independent subfamily. This works for rectangular and rank-deficient
ambient configurations; the nonsingular matrix is selected locally.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

theorem exists_nonsingular_row_restriction {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (A : Matrix ρ κ ℝ) (hA : LinearIndependent ℝ A.col) :
    ∃ r : κ ↪ ρ, (A.submatrix r id).det ≠ 0 := by
  classical
  obtain ⟨η, c, hc, hspan, hli⟩ := exists_linearIndependent' ℝ A.row
  let : Fintype η := Fintype.ofInjective c hc
  have hcols : A.rank = Fintype.card κ := by
    have ht : LinearIndependent ℝ A.transpose.row := hA
    simpa only [Matrix.rank_transpose] using ht.rank_matrix
  have hcard : Fintype.card η = Fintype.card κ := by
    calc
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range (A.row ∘ c))) :=
        linearIndependent_iff_card_eq_finrank_span.mp hli
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) := by rw [hspan]
      _ = A.rank := A.rank_eq_finrank_span_row.symm
      _ = _ := hcols
  let e : κ ≃ η := Fintype.equivOfCardEq hcard.symm
  let r : κ ↪ ρ := ⟨c ∘ e, hc.comp e.injective⟩
  have hr : LinearIndependent ℝ (A.submatrix r id).row := by
    change LinearIndependent ℝ (fun i j => A (c (e i)) j)
    simpa [Matrix.row, Function.comp_def] using! hli.comp e e.injective
  exact ⟨r, isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hr))⟩

/-- Equality of signs of every row-subset minor, allowing arbitrary column choices. -/
def SameMinorSigns {ρ ι : Type*} (A B : Matrix ρ ι ℝ) : Prop := by
  classical
  exact ∀ (R : Finset ρ) (c : R → ι),
    signCode (A.submatrix Subtype.val c).det = signCode (B.submatrix Subtype.val c).det

theorem SameMinorSigns.symm {ρ ι : Type*} {A B : Matrix ρ ι ℝ}
    (h : SameMinorSigns A B) : SameMinorSigns B A := fun R c => (h R c).symm

/-- The row-subset encoding includes any injectively indexed square row restriction. -/
theorem SameMinorSigns.det_submatrix {ρ ι κ : Type*} [Fintype κ] [DecidableEq κ]
    {A B : Matrix ρ ι ℝ} (h : SameMinorSigns A B) (r : κ ↪ ρ) (c : κ → ι) :
    signCode (A.submatrix r c).det = signCode (B.submatrix r c).det := by
  classical
  let R : Finset ρ := Finset.univ.map r
  let f : κ → R := fun i => ⟨r i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact r.injective (congrArg Subtype.val hij)
    · intro j
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp j.property
      exact ⟨i, Subtype.ext hi⟩
  let e : κ ≃ R := Equiv.ofBijective f hf
  have he : ∀ i, (e i).val = r i := fun _ => rfl
  have hd (M : Matrix ρ ι ℝ) :
      (M.submatrix r c).det = (M.submatrix Subtype.val (c ∘ e.symm)).det := by
    rw [← Matrix.det_submatrix_equiv_self e (M.submatrix Subtype.val (c ∘ e.symm))]
    congr 1
    ext i j
    simp [Matrix.submatrix, he]
  rw [hd A, hd B]
  exact h R (c ∘ e.symm)

/-- Independent columns stay independent when all minor signs are preserved. -/
theorem SameMinorSigns.linearIndependent {ρ ι κ : Type*} [Fintype ρ] [Fintype κ]
    {A B : Matrix ρ ι ℝ} (h : SameMinorSigns A B) (c : κ → ι)
    (hA : LinearIndependent ℝ (fun i => A.col (c i))) :
    LinearIndependent ℝ (fun i => B.col (c i)) := by
  classical
  obtain ⟨r, hr⟩ := exists_nonsingular_row_restriction (A.submatrix id c) hA
  have hr' : (A.submatrix r c).det ≠ 0 := by simpa using hr
  have hb : (B.submatrix r c).det ≠ 0 := fun hb =>
    hr' (((signCode_eq_iff _ _).mp (h.det_submatrix r c)).2.mpr hb)
  have hi := Matrix.linearIndependent_cols_of_det_ne_zero hb
  rw [linearIndependent_iff'] at hi ⊢
  intro s w hw
  apply hi s w
  funext i
  simpa [Matrix.col, Matrix.submatrix, Finset.sum_apply] using congrFun hw (r i)

theorem SameMinorSigns.linearIndependent_iff {ρ ι κ : Type*} [Fintype ρ] [Fintype κ]
    {A B : Matrix ρ ι ℝ} (h : SameMinorSigns A B) (c : κ → ι) :
    LinearIndependent ℝ (fun i => A.col (c i)) ↔
      LinearIndependent ℝ (fun i => B.col (c i)) :=
  ⟨h.linearIndependent c, h.symm.linearIndependent c⟩

/-- All minors, including the smaller ones, preserve span membership on independent supports. -/
theorem SameMinorSigns.mem_span_iff {ρ ι κ : Type*} [Fintype ρ] [Fintype κ]
    {A B : Matrix ρ ι ℝ} (h : SameMinorSigns A B) (c : κ → ι)
    (hA : LinearIndependent ℝ (fun j => A.col (c j))) (i : ι) :
    A.col i ∈ Submodule.span ℝ (Set.range (fun j => A.col (c j))) ↔
      B.col i ∈ Submodule.span ℝ (Set.range (fun j => B.col (c j))) := by
  have hB := h.linearIndependent c hA
  have he := h.linearIndependent_iff (fun j : Option κ => j.elim i c)
  apply not_iff_not.mp
  simpa [linearIndependent_option, Function.comp_def, hA, hB] using he

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.MinorHullRecovery` -/


/-!
# All-minor signs determine finite convex-hull membership

Choose a positive independent certificate, restrict to a nonsingular row
minor, and transfer the signs of its Cramer coefficients. The other rows are
handled by preservation of span membership, itself certified by all minors.
Thus no full-dimensionality or general-position hypothesis is needed.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

theorem submatrix_updateCol {ρ ι κ : Type*} [DecidableEq κ]
    (A : Matrix ρ ι ℝ) (r : κ → ρ) (c : κ → ι) (j : κ) (i : ι) :
    (A.submatrix r c).updateCol j (fun a => A (r a) i) =
      A.submatrix r (Function.update c j i) := by
  ext a b
  by_cases h : b = j <;> simp [Matrix.submatrix, h]

/-- Transfer a nonnegative linear certificate on an independent support. -/
theorem SameMinorSigns.nonnegative_certificate {ρ ι κ : Type*}
    [Fintype ρ] [Fintype κ] {A B : Matrix ρ ι ℝ}
    (h : SameMinorSigns A B) (c : κ → ι) (i : ι)
    (hA : LinearIndependent ℝ (fun j => A.col (c j)))
    (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (he : ∑ j, w j • A.col (c j) = A.col i) :
    ∃ v : κ → ℝ, (∀ j, 0 ≤ v j) ∧ ∑ j, v j • B.col (c j) = B.col i := by
  classical
  have hspan : A.col i ∈ Submodule.span ℝ (Set.range (fun j => A.col (c j))) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨w, he⟩
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    ((h.mem_span_iff c hA i).mp hspan)
  obtain ⟨r, hr⟩ := exists_nonsingular_row_restriction (A.submatrix id c) hA
  have ha : (A.submatrix r c).det ≠ 0 := by simpa using hr
  have hd := h.det_submatrix r c
  have hb : (B.submatrix r c).det ≠ 0 :=
    fun hb => ha (((signCode_eq_iff _ _).mp hd).2.mpr hb)
  have hwa : A.submatrix r c *ᵥ w = fun a => A (r a) i := by
    ext a
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix, Matrix.col,
      Finset.sum_apply, mul_comm] using congrFun he (r a)
  have hvb : B.submatrix r c *ᵥ v = fun a => B (r a) i := by
    ext a
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix, Matrix.col,
      Finset.sum_apply, mul_comm] using congrFun hv (r a)
  have hca := cramerWeights_eq_of_mulVec _ _ _ ha hwa
  have hcb := cramerWeights_eq_of_mulVec _ _ _ hb hvb
  have hn := cramerWeights_nonneg_iff (A.submatrix r c) (B.submatrix r c)
    (fun a => A (r a) i) (fun a => B (r a) i) hd
    (fun j => by simpa only [submatrix_updateCol] using
      h.det_submatrix r (Function.update c j i))
  rw [hca, hcb] at hn
  exact ⟨v, hn.mp hw, hv⟩

/-- Augmented columns of an arbitrary indexed configuration. -/
def augmentedMatrix {ι : Type*} {D : ℕ} (q : ι → Point D) :
    Matrix (Option (Fin D)) ι ℝ := Matrix.of fun r i => augmentedPoint (q i) r

/-- Equal all-minor signs transfer convex membership, including degenerate configurations. -/
theorem mem_indexedHull_of_sameMinorSigns {ι : Type*} {D : ℕ}
    (q q' : ι → Point D) (h : SameMinorSigns (augmentedMatrix q) (augmentedMatrix q'))
    (V : Finset ι) (i : ι) (hi : q i ∈ indexedHull q V) :
    q' i ∈ indexedHull q' V := by
  obtain ⟨r, c, w, _, _, hc, _, hl, hw, he⟩ := exists_independent_convexCertificate q V hi
  obtain ⟨v, hv, he'⟩ := h.nonnegative_certificate c i hl w (fun j => (hw j).le) he
  have hcoords := (sum_smul_augmentedPoint_eq_iff (fun j => q' (c j)) v (q' i)).mp he'
  exact mem_convexHull_of_exists_fintype v (fun j => q' (c j)) hv hcoords.1
    (fun j => ⟨c j, hc j, rfl⟩) hcoords.2

theorem mem_indexedHull_iff_of_sameMinorSigns {ι : Type*} {D : ℕ}
    (q q' : ι → Point D) (h : SameMinorSigns (augmentedMatrix q) (augmentedMatrix q'))
    (V : Finset ι) (i : ι) :
    q i ∈ indexedHull q V ↔ q' i ∈ indexedHull q' V :=
  ⟨mem_indexedHull_of_sameMinorSigns q q' h V i,
    mem_indexedHull_of_sameMinorSigns q' q h.symm V i⟩

/-- The polynomial family from P5 uses exactly the row-subset minor encoding above. -/
theorem sameMinorSigns_of_polynomial_signs {D m : ℕ}
    (z z' : Fin D → Fin m → Point D)
    (h : ∀ j : MinorIndex D m,
      signCode (MvPolynomial.eval (arrayAssignment z) (minorPolynomial j)) =
      signCode (MvPolynomial.eval (arrayAssignment z') (minorPolynomial j))) :
    SameMinorSigns (augmentedMatrix (gridSum z)) (augmentedMatrix (gridSum z')) := by
  classical
  intro R c
  have hdet (d : DecidableEq R) :
      @Matrix.det R d inferInstance ℝ inferInstance =
        @Matrix.det R (Classical.decEq R) inferInstance ℝ inferInstance :=
    congrArg (fun d => @Matrix.det R d inferInstance ℝ inferInstance) (Subsingleton.elim _ _)
  have hp := h ⟨R, c⟩
  simp only [eval_minorPolynomial, hdet] at hp
  simpa only [augmentedMatrix, augmentedPoint, Matrix.submatrix, Matrix.of_apply, hdet] using hp

/-- P5: the signs of all encoded polynomial minors determine every finite hull label. -/
theorem same_signs_same_hull_membership {D m : ℕ}
    (z z' : Fin D → Fin m → Point D)
    (h : ∀ j : MinorIndex D m,
      signCode (MvPolynomial.eval (arrayAssignment z) (minorPolynomial j)) =
      signCode (MvPolynomial.eval (arrayAssignment z') (minorPolynomial j)))
    (V : Finset (Grid D m)) (i : Grid D m) :
    gridSum z i ∈ indexedHull (gridSum z) V ↔
      gridSum z' i ∈ indexedHull (gridSum z') V :=
  mem_indexedHull_iff_of_sameMinorSigns _ _ (sameMinorSigns_of_polynomial_signs z z' h) V i

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.LabelCount` -/


/-!
# Count convex labels by minor signs and representative subsets

P5 makes the encoding injective. The sparse version explicitly retains
`SanyalBoxObstruction`; no geometric input is declared as an axiom.
-/

namespace VCDimConvexBound

/-- The minor sign vector of an additive array. -/
noncomputable def arrayMinorSigns {D m : ℕ} (z : Fin D → Fin m → Point D) :
    MinorIndex D m → Fin 3 :=
  fun j => signCode (MvPolynomial.eval (arrayAssignment z) (minorPolynomial j))

theorem arrayMinorSigns_mem {D m : ℕ} (z : Fin D → Fin m → Point D) :
    arrayMinorSigns z ∈ minorSignPatterns D m := by
  classical
  simp only [minorSignPatterns, ternaryPatterns, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨arrayAssignment z, fun _ => rfl⟩

/-- Any family of representative subsets covering all labels gives a product bound. -/
theorem card_convexLabels_le_signs_mul_generators {D m : ℕ}
    (G : Finset (Finset (Grid D m)))
    (hgen : ∀ S ∈ convexLabels D m,
      ∃ (z : Fin D → Fin m → Point D) (V : Finset (Grid D m)),
        V ∈ G ∧ ∀ i, i ∈ S ↔ gridSum z i ∈ indexedHull (gridSum z) V) :
    (convexLabels D m).card ≤ (minorSignPatterns D m).card * G.card := by
  classical
  choose z V hV hlabels using fun S : ↑(convexLabels D m) => hgen S S.property
  let encode : ↑(convexLabels D m) → ↑(minorSignPatterns D m) × ↑G :=
    fun S => (⟨arrayMinorSigns (z S), arrayMinorSigns_mem (z S)⟩, ⟨V S, hV S⟩)
  have hinj : Function.Injective encode := by
    intro S T he
    have hs : arrayMinorSigns (z S) = arrayMinorSigns (z T) :=
      congrArg (fun e => e.1.val) he
    have hv : V S = V T := congrArg (fun e => e.2.val) he
    apply Subtype.ext
    ext i
    rw [hlabels S i, hlabels T i, ← hv]
    exact same_signs_same_hull_membership (z S) (z T) (fun j => congrFun hs j) (V S) i
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective encode hinj

/-- Candidate representative subsets of density strictly less than one sixteenth. -/
noncomputable def sparseSubsets (ι : Type*) [Fintype ι] : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun V => 16 * V.card < Fintype.card ι

@[simp] theorem mem_sparseSubsets {ι : Type*} [Fintype ι] (V : Finset ι) :
    V ∈ sparseSubsets ι ↔ 16 * V.card < Fintype.card ι := by
  classical
  simp [sparseSubsets]

/-- P4 and P5: the number of convex labels is at most the product of the two code counts. -/
theorem card_convexLabels_le_signs_mul_sparse_of_sanyal (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D) :
    (convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))).card ≤
      (minorSignPatterns D (2 ^ (8 * (D + 1) ^ (D - 1)))).card *
        (sparseSubsets (Grid D (2 ^ (8 * (D + 1) ^ (D - 1))))).card := by
  apply card_convexLabels_le_signs_mul_generators
  intro S hSlabel
  obtain ⟨z, V, _, hcard, hlabels⟩ := exists_sparse_hull_encoding_of_sanyal D hD hS S hSlabel
  exact ⟨z, V, by simpa using hcard, hlabels⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SparseSubsetCount` -/


/-!
# A weighted count of sparse representative subsets

When M = 16k > 0, give a subset V weight 4^(M-|V|). Summing over all subsets
gives 5^M. Every sparse subset has weight at least 4^(15k), and
5^16 < 2^38 yields U < 2^(8k). This avoids logarithmic entropy estimates.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- A weighted binomial count for representative subsets. -/
theorem card_sparseSubsets_mul_weight_le (ι : Type*) [Fintype ι]
    (k : ℕ) (hcard : Fintype.card ι = 16 * k) :
    (sparseSubsets ι).card * 4 ^ (15 * k) ≤ 5 ^ (16 * k) := by
  classical
  calc
    (sparseSubsets ι).card * 4 ^ (15 * k) =
        ∑ V ∈ sparseSubsets ι, 4 ^ (15 * k) := by simp
    _ ≤ ∑ V ∈ sparseSubsets ι, 4 ^ (Fintype.card ι - V.card) := by
      apply Finset.sum_le_sum
      intro V hV
      have hs := mem_sparseSubsets V |>.mp hV
      apply Nat.pow_le_pow_right (by decide)
      omega
    _ ≤ ∑ V : Finset ι, 4 ^ (Fintype.card ι - V.card) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 5 ^ (16 * k) := by
      simpa [hcard] using Fintype.sum_pow_mul_eq_add_pow ι (1 : ℕ) 4

/-- Sparse subsets use strictly less than half the bit budget. -/
theorem card_sparseSubsets_lt_two_pow_half (ι : Type*) [Fintype ι]
    (k : ℕ) (hk : 0 < k) (hcard : Fintype.card ι = 16 * k) :
    (sparseSubsets ι).card < 2 ^ (8 * k) := by
  have hnum : 5 ^ (16 * k) < (2 : ℕ) ^ (38 * k) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  have heq : (2 : ℕ) ^ (38 * k) = 2 ^ (8 * k) * 4 ^ (15 * k) := by
    calc
      2 ^ (38 * k) = 2 ^ (8 * k + 2 * (15 * k)) := by congr 1; omega
      _ = 2 ^ (8 * k) * (2 ^ 2) ^ (15 * k) := by rw [pow_add, pow_mul 2 2]
      _ = _ := by norm_num
  have h := (card_sparseSubsets_mul_weight_le ι k hcard).trans_lt hnum
  rw [heq] at h
  exact Nat.lt_of_mul_lt_mul_right h

/-- A root-free form of the half-budget estimate. -/
theorem card_sparseSubsets_sq_lt (ι : Type*) [Fintype ι]
    (k : ℕ) (hk : 0 < k) (hcard : Fintype.card ι = 16 * k) :
    (sparseSubsets ι).card ^ 2 < 2 ^ Fintype.card ι := by
  calc
    (sparseSubsets ι).card ^ 2 < (2 ^ (8 * k)) ^ 2 :=
      Nat.pow_lt_pow_left (card_sparseSubsets_lt_two_pow_half ι k hk hcard) (by decide)
    _ = 2 ^ Fintype.card ι := by rw [hcard, ← pow_mul]; congr 1; omega

/-- The chosen additive grid has a positive cardinality divisible by sixteen. -/
theorem explicit_grid_card_eq_sixteen_mul (D : ℕ) (hD : 2 ≤ D) :
    ∃ k : ℕ, 0 < k ∧
      Fintype.card (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))) = 16 * k := by
  let e := 8 * (D + 1) ^ (D - 1) * D
  have hp : 0 < (D + 1) ^ (D - 1) := by positivity
  have he : 4 ≤ e := by dsimp [e]; nlinarith
  refine ⟨2 ^ (e - 4), by positivity, ?_⟩
  rw [card_grid, ← pow_mul]
  change 2 ^ e = 16 * 2 ^ (e - 4)
  calc
    2 ^ e = 2 ^ (4 + (e - 4)) := by congr 1; omega
    _ = _ := by rw [pow_add]; norm_num

/-- P7: the representative-subset factor is strictly below 2^(M/2). -/
theorem card_sparseSubsets_explicit_sq_lt (D : ℕ) (hD : 2 ≤ D) :
    (sparseSubsets (Grid D (2 ^ (8 * (D + 1) ^ (D - 1))))).card ^ 2 <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  obtain ⟨k, hk, hcard⟩ := explicit_grid_card_eq_sixteen_mul D hD
  simpa using card_sparseSubsets_sq_lt _ k hk hcard

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.Shattering` -/


/-!
# From counting additive arrays to a VCₙ bound

This is the final reduction of section 7 of the paper argument. Shattering
an `n`-dimensional grid realizes every label on an `(n + 1)`-dimensional
array. We place the new translation coordinate first; permuting coordinates
gives the presentation with the translation coordinate last.

The counting inequality remains an explicit hypothesis. This file does not
prove that inequality or the unconditional bound for convex sets.
-/

namespace VCDimConvexBound

/-- Slice an arbitrary label by its first coordinate, and use the shattering
translations as the first sequence of a larger additive array. -/
theorem realizes_of_shattering {G : Type*} [AddCommGroup G]
    {n m : ℕ} {C : Set G}
    (x : Fin n → Fin m → G) (y : Set (Grid n m) → G)
    (hxy : ∀ i s, y s + ∑ k, x k (i k) ∈ C ↔ i ∈ s)
    (S : Set (Grid (n + 1) m)) : Realizes C S := by
  let z : Fin (n + 1) → Fin m → G :=
    Fin.cons (fun j => y {i | Fin.cons j i ∈ S}) x
  refine ⟨z, fun i => ?_⟩
  simpa [gridSum, z, Fin.sum_univ_succ, Fin.tail, Fin.cons_self_tail] using
    hxy (Fin.tail i) {j | Fin.cons (i 0) j ∈ S}

/-- Shattering forces all labels to occur, even while keeping `C` fixed. -/
theorem convexLabels_eq_univ_of_shattering {n m : ℕ}
    {C : Set (Point (n + 1))} (hC : Convex ℝ C)
    (x : Fin n → Fin m → Point (n + 1))
    (y : Set (Grid n m) → Point (n + 1))
    (hxy : ∀ i s, y s + ∑ k, x k (i k) ∈ C ↔ i ∈ s) :
    convexLabels (n + 1) m = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro S
  exact mem_convexLabels.mpr ⟨C, hC, realizes_of_shattering x y hxy S⟩

/-- A strict count of convex labels gives the actual FC predicate. -/
theorem hasAddVCNDimAtMost_of_label_count (n d : ℕ)
    (hcount : (convexLabels (n + 1) (d + 1)).card < 2 ^ ((d + 1) ^ (n + 1)))
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n d := by
  intro x y hxy
  have hfull := convexLabels_eq_univ_of_shattering hC x y hxy
  simp [hfull] at hcount

/-- The side-length version keeps the off-by-one conversion explicit. -/
theorem hasAddVCNDimAtMost_of_label_count_side (n m : ℕ) (hm : 0 < m)
    (hcount : (convexLabels (n + 1) m).card < 2 ^ (m ^ (n + 1)))
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (m - 1) := by
  cases m with
  | zero => omega
  | succ d =>
    simpa only [Nat.succ_sub_one] using
      hasAddVCNDimAtMost_of_label_count n d hcount C hC

/-- The proposed explicit bound follows if its missing counting estimate is supplied. -/
theorem explicit_bound_of_label_count (n : ℕ)
    (hcount : (convexLabels (n + 1) (2 ^ (8 * (n + 2) ^ n))).card <
      2 ^ ((2 ^ (8 * (n + 2) ^ n)) ^ (n + 1)))
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) := by
  exact hasAddVCNDimAtMost_of_label_count_side n _ (by positivity) hcount C hC

/-- This conditional result has exactly the quantifiers needed by the FC existence problem. -/
theorem exists_bound_of_label_count
    (hcount : ∀ n : ℕ, 1 ≤ n →
      (convexLabels (n + 1) (2 ^ (8 * (n + 2) ^ n))).card <
        2 ^ ((2 ^ (8 * (n + 2) ^ n)) ^ (n + 1)))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d := by
  exact ⟨bound n, fun C hC => explicit_bound_of_label_count n (hcount n hn) C hC⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.ConditionalBound` -/


/-!
# The explicit VC bound, conditional only on Sanyal and Warren

P7 supplies the previously assumed label-count estimate. These final theorems
still take the two unproved core propositions as explicit arguments; they do
not constitute an unconditional solution of the Formal Conjectures problem.
-/

namespace VCDimConvexBound

/-- Two factors each below the square-root budget have product below the total budget. -/
theorem mul_lt_of_sq_lt {a b c : ℕ} (ha : a ^ 2 < c) (hb : b ^ 2 < c) :
    a * b < c := by
  have hsq : (a * b) ^ 2 < c ^ 2 := by
    rw [mul_pow, pow_two c]
    calc
      a ^ 2 * b ^ 2 ≤ c * b ^ 2 := Nat.mul_le_mul_right _ ha.le
      _ < c * c := Nat.mul_lt_mul_of_pos_left hb (by omega)
  nlinarith

/-- P7, including all constants and every D≥2, conditional on the two core inputs. -/
theorem card_convexLabels_lt_of_sanyal_warren (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D) (hW : WarrenStrictBound) :
    (convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))).card <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  exact (card_convexLabels_le_signs_mul_sparse_of_sanyal D hD hS).trans_lt
    (mul_lt_of_sq_lt (card_minorSignPatterns_explicit_sq_lt_of_warren hW D hD)
      (card_sparseSubsets_explicit_sq_lt D hD))

/-- The original explicit bound now requires only Sanyal and Warren, with no hcount. -/
theorem explicit_bound_of_sanyal_warren (n : ℕ) (hn : 1 ≤ n)
    (hS : SanyalBoxObstruction (n + 1)) (hW : WarrenStrictBound)
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) := by
  apply explicit_bound_of_label_count n _ C hC
  simpa [Nat.add_assoc] using
    card_convexLabels_lt_of_sanyal_warren (n + 1) (by omega) hS hW

/-- The FC existence statement with exactly the two unproved core inputs remaining. -/
theorem exists_bound_of_sanyal_warren
    (hS : ∀ D : ℕ, 2 ≤ D → SanyalBoxObstruction D) (hW : WarrenStrictBound)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d := by
  exact ⟨bound n, fun C hC => explicit_bound_of_sanyal_warren n hn
    (hS (n + 1) (by omega)) hW C hC⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.MilnorConditionalBound` -/


/-!
# The original explicit VC bound using a coarse hypersurface input

This is an alternative conditional proof, not a proof of either remaining
core. Sanyal and the hypersurface component bound are explicit arguments.
Warren's theorem is not an argument of these declarations.
-/

namespace VCDimConvexBound

theorem card_convexLabels_lt_of_sanyal_hypersurface (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D) (hM : HypersurfaceComponentBound) :
    (convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))).card <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  exact (card_convexLabels_le_signs_mul_sparse_of_sanyal D hD hS).trans_lt
    (mul_lt_of_sq_lt (card_minorSignPatterns_explicit_sq_lt_of_hypersurface hM D hD)
      (card_sparseSubsets_explicit_sq_lt D hD))

/-- The same explicit bound, assuming Sanyal and a coarse component estimate. -/
theorem explicit_bound_of_sanyal_hypersurface (n : ℕ) (hn : 1 ≤ n)
    (hS : SanyalBoxObstruction (n + 1)) (hM : HypersurfaceComponentBound)
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) := by
  apply explicit_bound_of_label_count n _ C hC
  simpa [Nat.add_assoc] using
    card_convexLabels_lt_of_sanyal_hypersurface (n + 1) (by omega) hS hM

/-- The FC existence conclusion with the new route's two obligations still explicit. -/
theorem exists_bound_of_sanyal_hypersurface
    (hS : ∀ D : ℕ, 2 ≤ D → SanyalBoxObstruction D) (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d := by
  exact ⟨bound n, fun C hC => explicit_bound_of_sanyal_hypersurface n hn
    (hS (n + 1) (by omega)) hM C hC⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.SanyalOddMap` -/


/-!
# Reduction of Sanyal to a precise odd-map zero principle

The continuous odd map is now constructed. Only its topological obstruction
is an unproved input. This input is a proposition passed as an argument,
not a new axiom. Together with the hypersurface component bound it yields
the original explicit VC bound.
-/

namespace VCDimConvexBound

/-- The remaining Borsuk-Ulam-type input, in exactly the spaces used here.
The domain has dimension 2D and the target has dimension 2D-1. This definition
is not a proof of the principle. The zero must occur away from the origin. -/
def OddMapZeroCore : Prop :=
  ∀ (D : ℕ), 0 < D →
    ∀ f : HexagonDomain D → LinearMap.ker (cayleyColorSum D D),
      Continuous f → (∀ x, f (-x) = -f x) → ∃ x, x ≠ 0 ∧ f x = 0

/-- Restricting the choices in each color preserves convex independence of all sums. -/
theorem convexIndependent_gridSum_restrict {r m m' D : ℕ}
    (z : Fin r → Fin m' → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (e : Fin m ↪ Fin m') :
    ConvexIndependent ℝ (gridSum (fun k j => z k (e j))) := by
  let E : Grid r m ↪ Grid r m' :=
    ⟨fun i k => e (i k), fun a b h => funext (fun k => e.injective (congrFun h k))⟩
  exact hz.comp_embedding E

/-- Three choices per color contradict the odd-map zero principle. -/
theorem not_convexIndependent_three_of_oddMapZero (hB : OddMapZeroCore)
    (D : ℕ) (hD : 0 < D) (z : Fin D → Fin 3 → Point D) :
    ¬ ConvexIndependent ℝ (gridSum z) := by
  intro hz
  obtain ⟨x, hx, hf⟩ := hB D hD (hexagonKernelMap hD z)
    (continuous_hexagonKernelMap hD z) (hexagonKernelMap_neg hD z)
  exact hexagonKernelMap_ne_zero hD z hz x hx hf

/-- Restrict a putative Sanyal counterexample to three points per color. -/
theorem sanyalBoxObstruction_of_oddMapZero (hB : OddMapZeroCore)
    (D : ℕ) (hD : 2 ≤ D) : SanyalBoxObstruction D := by
  intro z hz
  let e : Fin 3 ↪ Fin (D + 1) :=
    ⟨Fin.castLE (by omega), Fin.castLE_injective (by omega)⟩
  exact not_convexIndependent_three_of_oddMapZero hB D (by omega)
    (fun k j => z k (e j)) (convexIndependent_gridSum_restrict z hz e)

/-- The original bound, now with the two remaining cores stated directly. -/
theorem explicit_bound_of_oddMapZero_hypersurface
    (hB : OddMapZeroCore) (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) :=
  explicit_bound_of_sanyal_hypersurface n hn
    (sanyalBoxObstruction_of_oddMapZero hB (n + 1) (by omega)) hM C hC

/-- The FC existence conclusion retains only the odd-map and component inputs. -/
theorem exists_bound_of_oddMapZero_hypersurface
    (hB : OddMapZeroCore) (hM : HypersurfaceComponentBound) (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d :=
  ⟨bound n, fun C hC => explicit_bound_of_oddMapZero_hypersurface hB hM n hn C hC⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonConeCore` -/


/-!
# A finite cone-kernel input sufficient for the original bound

Only the specific linear pieces of the hexagon map need a nonnegative kernel
certificate. This is weaker than the general odd-map zero principle. The
existence of such a certificate for every configuration remains unproved.
-/

namespace VCDimConvexBound

/-- The remaining geometric input, expressed using finitely many linear systems.
For each configuration, at least one of the `6^D` pieces must have a nonnegative
kernel vector of total mass one. This definition is not a proof. -/
def HexConeKernelCore : Prop :=
  ∀ (D : ℕ), 2 ≤ D → ∀ z : Fin D → Fin 3 → Point D,
    ∃ s : Fin D → Fin 6, ∃ t : HexagonDomain D,
      HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0

/-- The general odd-map principle supplies the specialized cone certificate. -/
theorem hexConeKernelCore_of_oddMapZero (hB : OddMapZeroCore) : HexConeKernelCore := by
  intro D hD z
  have hD' : 0 < D := by omega
  obtain ⟨x, hx, hf⟩ := hB D hD' (hexagonKernelMap hD' z)
    (continuous_hexagonKernelMap hD' z) (hexagonKernelMap_neg hD' z)
  apply (hexagon_zero_iff_normalized_piece_kernel z).mp
  exact ⟨x, hx, congrArg Subtype.val hf⟩

/-- A specialized nonnegative certificate already contradicts convex independence. -/
theorem not_convexIndependent_three_of_hexConeKernel (hK : HexConeKernelCore)
    (D : ℕ) (hD : 2 ≤ D) (z : Fin D → Fin 3 → Point D) :
    ¬ ConvexIndependent ℝ (gridSum z) := by
  intro hz
  obtain ⟨x, hx, hf⟩ := (hexagon_zero_iff_normalized_piece_kernel z).mpr (hK D hD z)
  exact hexagonCayleyMap_ne_zero (by omega) z hz x hx hf

/-- Restricting to three choices connects the cone certificate to Sanyal. -/
theorem sanyalBoxObstruction_of_hexConeKernel (hK : HexConeKernelCore)
    (D : ℕ) (hD : 2 ≤ D) : SanyalBoxObstruction D := by
  intro z hz
  let e : Fin 3 ↪ Fin (D + 1) :=
    ⟨Fin.castLE (by omega), Fin.castLE_injective (by omega)⟩
  exact not_convexIndependent_three_of_hexConeKernel hK D hD
    (fun k j => z k (e j)) (convexIndependent_gridSum_restrict z hz e)

/-- The original explicit bound needs only the cone and hypersurface cores. -/
theorem explicit_bound_of_hexConeKernel_hypersurface
    (hK : HexConeKernelCore) (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) :=
  explicit_bound_of_sanyal_hypersurface n hn
    (sanyalBoxObstruction_of_hexConeKernel hK (n + 1) (by omega)) hM C hC

/-- The FC existence conclusion with the specialized geometric input. -/
theorem exists_bound_of_hexConeKernel_hypersurface
    (hK : HexConeKernelCore) (hM : HypersurfaceComponentBound) (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d :=
  ⟨bound n, fun C hC => explicit_bound_of_hexConeKernel_hypersurface hK hM n hn C hC⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.HexagonConeExistence` -/


/-!
# Proof of the geometric cone-kernel core

Transport actual vertex images in the Cayley color-sum kernel to R^(2D-1).
The unconditional odd vertex theorem supplies a barycentric zero. The
sector interpolation bridge turns it into the normalized nonnegative
kernel certificate. The original VC bound now needs only the independent
hypersurface component bound.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Every actual hexagon map has a normalized nonnegative piece-kernel
certificate. No convex-independence or general-position assumption is used. -/
theorem hexagon_exists_normalized_piece_kernel (D : ℕ) (hD : 0 < D)
    (z : Fin D → Fin 3 → Point D) :
    ∃ s : Fin D → Fin 6, ∃ t : HexagonDomain D,
      HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0 := by
  let E : LinearMap.ker (cayleyColorSum D D) ≃ₗ[ℝ] Point (2 * D - 1) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [finrank_ker_cayleyColorSum D hD, Point])
  let p : HexVertex D → Point (2 * D - 1) :=
    fun v => E (hexagonKernelMap hD z (hexDomainVertex v))
  have hp : ∀ v, p (hexVertexOpposite v) = -p v := by
    intro v
    dsimp [p]
    rw [hexDomainVertex_opposite, hexagonKernelMap_neg, map_neg]
  obtain ⟨s, x, hm, hx, hz⟩ := hexOdd_exists_barycentric_zero hD p hp
  have hk : (∑ v : hexFacet s, x v • hexagonKernelMap hD z (hexDomainVertex v.val)) = 0 := by
    apply E.injective
    simpa only [map_sum, map_smul, map_zero] using hz
  have ha : (∑ v : hexFacet s, x v • hexagonCayleyMap z (hexDomainVertex v.val)) = 0 := by
    have he := congrArg Subtype.val hk
    simpa [hexagonKernelMap] using he
  exact ⟨s, exists_hexPiece_kernel_of_facet_zero z s x hm hx ha⟩

/-- The previously isolated geometric core is now proved. -/
theorem hexConeKernelCore : HexConeKernelCore := by
  intro D hD z
  exact hexagon_exists_normalized_piece_kernel D (by omega) z

/-- Sanyal's required box obstruction, with no geometric core hypothesis. -/
theorem sanyalBoxObstruction (D : ℕ) (hD : 2 ≤ D) : SanyalBoxObstruction D :=
  sanyalBoxObstruction_of_hexConeKernel hexConeKernelCore D hD

/-- The original explicit VC bound now has only the hypersurface component
bound as an unproved input. -/
theorem explicit_bound_of_hypersurface (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) :=
  explicit_bound_of_hexConeKernel_hypersurface hexConeKernelCore hM n hn C hC

/-- The FC existence conclusion, conditional only on the component bound. -/
theorem exists_bound_of_hypersurface (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d :=
  exists_bound_of_hexConeKernel_hypersurface hexConeKernelCore hM n hn

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.FinalBound` -/


/-!
# The explicit VC bound without unproved geometric or sign-count inputs

The direct polynomial sign count supplies the existing numerical budget.
The proved Sanyal obstruction and label-count reduction then give the
original bound and the Formal Conjectures existence statement.
-/

namespace VCDimConvexBound

/-- All minor sign patterns obey the coarse budget, unconditionally. -/
theorem card_minorSignPatterns_le_direct (D m : ℕ) (hD : 1 ≤ D) (hm : 0 < m) :
    (minorSignPatterns D m).card ≤
      (4 * D * (2 ^ (D + 1) * (m ^ D) ^ (D + 1)) + 2) ^ (D ^ 2 * m + 2) := by
  have h := card_ternaryPatterns_le_coarse_direct D hD
    (minorPolynomial (D := D) (m := m)) totalDegree_minorPolynomial_le
  simp only [card_arrayVar] at h
  change (minorSignPatterns D m).card ≤ _ at h
  exact h.trans (by gcongr; exact card_minorIndex_le D m hm)

/-- The previously established numerical estimates apply to the direct sign count. -/
theorem card_minorSignPatterns_le_two_pow_direct (D L : ℕ) (hD : 1 ≤ D) (hL : 8 ≤ L) :
    (minorSignPatterns D (2 ^ L)).card ≤ 2 ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
  have hm : 0 < (2 : ℕ) ^ L := by positivity
  have hp : D ^ 2 * 2 ^ L + 2 ≤ 2 * (D + 1) ^ 2 * 2 ^ L := by
    calc
      _ ≤ (D ^ 2 + 2) * 2 ^ L := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith : D ^ 2 + 2 ≤ 2 * (D + 1) ^ 2)
  have he : (2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2) ≤
      4 * L * (D + 1) ^ 4 * 2 ^ L := by
    calc
      _ ≤ (2 * L * (D + 1) ^ 2) * (2 * (D + 1) ^ 2 * 2 ^ L) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ _ := card_minorSignPatterns_le_direct D (2 ^ L) hD hm
    _ ≤ (2 ^ (2 * L * (D + 1) ^ 2)) ^ (D ^ 2 * 2 ^ L + 2) :=
      Nat.pow_le_pow_left (minor_hypersurface_base_le_two_pow D L hD hL) _
    _ = 2 ^ ((2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

/-- At the original explicit side length, the square sign count is strictly below 2^M. -/
theorem card_minorSignPatterns_explicit_sq_lt_direct (D : ℕ) (hD : 2 ≤ D) :
    (minorSignPatterns D (2 ^ (8 * (D + 1) ^ (D - 1)))).card ^ 2 <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  let L := 8 * (D + 1) ^ (D - 1)
  let m := 2 ^ L
  have hL : 8 ≤ L := by
    have h : 0 < (D + 1) ^ (D - 1) := by positivity
    dsimp [L]
    omega
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hb : 8 * L * (D + 1) ^ 4 < m := explicit_sign_exponent_budget D hD
  have hmD : m ^ 2 ≤ m ^ D := Nat.pow_le_pow_right hm0 hD
  have he : (4 * L * (D + 1) ^ 4 * m) * 2 < m ^ D := by
    calc
      _ = (8 * L * (D + 1) ^ 4) * m := by ring
      _ < m * m := Nat.mul_lt_mul_of_pos_right hb hm0
      _ ≤ m ^ D := by simpa [pow_two] using hmD
  have ht := card_minorSignPatterns_le_two_pow_direct D L (by omega) hL
  calc
    _ ≤ (2 ^ (4 * L * (D + 1) ^ 4 * m)) ^ 2 := Nat.pow_le_pow_left ht 2
    _ = 2 ^ ((4 * L * (D + 1) ^ 4 * m) * 2) := (pow_mul _ _ _).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) he

/-- Fewer than all labels are realized at the original explicit side length. -/
theorem card_convexLabels_lt_explicit (D : ℕ) (hD : 2 ≤ D) :
    (convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))).card <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  exact (card_convexLabels_le_signs_mul_sparse_of_sanyal D hD
    (sanyalBoxObstruction D hD)).trans_lt
    (mul_lt_of_sq_lt (card_minorSignPatterns_explicit_sq_lt_direct D hD)
      (card_sparseSubsets_explicit_sq_lt D hD))

/-- Every convex set has additive VC_n dimension at most 2^(8*(n+2)^n)-1 for n≥1. -/
theorem explicit_bound (n : ℕ) (hn : 1 ≤ n)
    (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) := by
  apply explicit_bound_of_label_count n _ C hC
  simpa [Nat.add_assoc] using card_convexLabels_lt_explicit (n + 1) (by omega)

/-- The Formal Conjectures uniform finite-bound existence statement, for every n≥1. -/
theorem exists_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d :=
  ⟨bound n, fun C hC => explicit_bound n hn C hC⟩

end VCDimConvexBound


/-! ## Source module `VCDimConvexBound.FCStatement` -/


/-!
# The exact pinned Formal Conjectures existence statement

The statement below is copied from
`FormalConjectures/Other/VCDimConvex.lean` at the pinned revision.
The verification script checks the entire binder and conclusion text
against that source, modulo whitespace. The proof uses only the local
proved bound, not the conjecture declaration from the upstream file.
-/

namespace VCDimConvexBound

theorem fc_exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d :=
  exists_bound n hn

end VCDimConvexBound


namespace VCDimConvexBoundLean4Web

/-- The complete binder and conclusion of the pinned Formal Conjectures target. -/
theorem formal_conjectures_target (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d :=
  VCDimConvexBound.fc_exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one n hn

#check VCDimConvexBound.explicit_bound
#check formal_conjectures_target
#print axioms VCDimConvexBound.explicit_bound
#print axioms formal_conjectures_target

end VCDimConvexBoundLean4Web
