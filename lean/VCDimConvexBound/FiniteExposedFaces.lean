import VCDimConvexBound.ConvexCertificates
import Mathlib.Analysis.Convex.Exposed

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
