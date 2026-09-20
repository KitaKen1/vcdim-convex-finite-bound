import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

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
    rw [signCode, if_pos hn]
    change a - t < 0 ∧ a + t < 0
    constructor <;> linarith
  · by_cases hz : a = 0
    · subst a
      simp [signCode, encodeSign, ht]
    · have hp : 0 < a := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have h := hsmall hz
      rw [abs_of_pos hp] at h
      rw [signCode, if_neg hn, if_neg hz]
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
