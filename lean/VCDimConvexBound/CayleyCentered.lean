import VCDimConvexBound.CenteredFaces
import VCDimConvexBound.ColorfulComplex

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
  rw [dif_pos hex]
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
