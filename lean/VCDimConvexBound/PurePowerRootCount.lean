import VCDimConvexBound.FinitePolynomialEvaluation
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Order

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
  simp only [Finset.mul_sum, MvPolynomial.monomial_mul, one_mul, map_sum]

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
        rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul, hdecomp]
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
