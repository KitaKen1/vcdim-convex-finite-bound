import VCDimConvexBound.HullEncoding
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

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
