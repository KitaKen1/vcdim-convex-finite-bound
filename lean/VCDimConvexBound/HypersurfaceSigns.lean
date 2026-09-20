import VCDimConvexBound.WarrenApplication
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.SetTheory.Cardinal.Finite

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
      cases hs : s i <;> simp only [hs, Bool.false_eq_true, if_false, if_true] at h
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
