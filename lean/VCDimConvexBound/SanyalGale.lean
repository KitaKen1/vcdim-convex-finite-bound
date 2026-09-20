import VCDimConvexBound.SanyalCertificates
import Mathlib.LinearAlgebra.Dual.Lemmas

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
