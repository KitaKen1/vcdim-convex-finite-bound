import VCDimConvexBound.PolynomialSignRegion
import VCDimConvexBound.WarrenApplication

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
    cases hsi : s.val i <;> simp only [hsi, Bool.false_eq_true, if_false, if_true] at hi
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
