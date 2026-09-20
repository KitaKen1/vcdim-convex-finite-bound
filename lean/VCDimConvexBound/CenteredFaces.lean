import VCDimConvexBound.FiniteExposedFaces

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
