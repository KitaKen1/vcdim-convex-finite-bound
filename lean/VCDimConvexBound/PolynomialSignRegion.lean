import VCDimConvexBound.BarrierMaximum
import VCDimConvexBound.SignPatterns

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
  · simpa only [hs, Bool.false_eq_true, if_false] using
      isClosed_le (MvPolynomial.continuous_eval (f i)) continuous_const
  · simpa only [hs, if_true] using
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
  cases hs : s i <;> simp only [hs, Bool.false_eq_true, if_false, if_true] at hwi ⊢
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
    · simpa only [hi, Bool.false_eq_true, if_false] using
        isOpen_lt (MvPolynomial.continuous_eval (f i)) continuous_const
    · simpa only [hi, if_true] using
        isOpen_lt continuous_const (MvPolynomial.continuous_eval (f i))
  apply Filter.mem_of_superset (hopen.mem_nhds hs)
  intro y hy i
  have hi := hy i
  cases hsi : s i <;> simp only [hsi, Bool.false_eq_true, if_false, if_true] at hi ⊢
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
    cases hs : s i <;> simp only [hs, Bool.false_eq_true, if_false, if_true] at hi ⊢
    · exact hi.le
    · exact hi.le
  obtain ⟨b, hb, hbpos, hm⟩ := exists_barrier_localMax_mem (∏ i, f i) d hdeg ε hε
    (polynomialWeakSignRegion f s) (isClosed_polynomialWeakSignRegion f s)
    (polynomialWeakSignRegion_mem_nhds f s) a haw hapos
  exact ⟨b, strict_signs_of_mem_weakSignRegion f s b hb
    (eval_ne_zero_of_barrier_pos (∏ i, f i) d ε hε b hbpos), hm⟩

end VCDimConvexBound
