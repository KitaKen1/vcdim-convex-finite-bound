import VCDimConvexBound.AffineSliceInterval
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Scalar crossing parity on a closed interval

An affine scalar function with nonzero endpoint values has an interior zero
exactly when its endpoint signs differ. Its positive endpoint count modulo
two therefore detects that zero. This is the scalar ingredient, not yet the
cochain identity on the faces of a simplex.
-/

namespace VCDimConvexBound

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- A nonconstant affine scalar function has at most one zero. -/
theorem affineScalar_zero_unique {c d s t : ℝ} (hd : d ≠ 0)
    (hs : c + s * d = 0) (ht : c + t * d = 0) : s = t := by
  apply mul_right_cancel₀ hd
  linarith

/-- An interior zero is equivalent to opposite strict endpoint signs. -/
theorem affineScalar_crossing_iff {c d L U : ℝ} (hd : d ≠ 0) (hLU : L < U) :
    (∃ t, L < t ∧ t < U ∧ c + t * d = 0) ↔
      (c + L * d < 0 ∧ 0 < c + U * d) ∨
      (0 < c + L * d ∧ c + U * d < 0) := by
  rcases lt_or_gt_of_ne hd with hd | hd
  · constructor
    · rintro ⟨t, htL, htU, ht⟩
      have h₁ := mul_pos (sub_pos.mpr htL) (neg_pos.mpr hd)
      have h₂ := mul_pos (sub_pos.mpr htU) (neg_pos.mpr hd)
      right
      constructor <;> nlinarith
    · intro h
      have hdec := mul_pos (sub_pos.mpr hLU) (neg_pos.mpr hd)
      have hsign : 0 < c + L * d ∧ c + U * d < 0 := by
        rcases h with h | h
        · exfalso; nlinarith [h.1, h.2]
        · exact h
      refine ⟨-c / d, ?_, ?_, sliceCoeff_at_root c d (ne_of_lt hd)⟩
      · rw [lt_div_iff_of_neg hd]
        linarith [hsign.1]
      · rw [div_lt_iff_of_neg hd]
        linarith [hsign.2]
  · constructor
    · rintro ⟨t, htL, htU, ht⟩
      have h₁ := mul_pos (sub_pos.mpr htL) hd
      have h₂ := mul_pos (sub_pos.mpr htU) hd
      left
      constructor <;> nlinarith
    · intro h
      have hinc := mul_pos (sub_pos.mpr hLU) hd
      have hsign : c + L * d < 0 ∧ 0 < c + U * d := by
        rcases h with h | h
        · exact h
        · exfalso; nlinarith [h.1, h.2]
      refine ⟨-c / d, ?_, ?_, sliceCoeff_at_root c d (ne_of_gt hd)⟩
      · rw [lt_div_iff₀ hd]
        linarith [hsign.1]
      · rw [div_lt_iff₀ hd]
        linarith [hsign.2]

/-- The crossing detected by the signs is a unique interior zero. -/
theorem affineScalar_unique_crossing_iff {c d L U : ℝ} (hd : d ≠ 0) (hLU : L < U) :
    (∃! t, L < t ∧ t < U ∧ c + t * d = 0) ↔
      (c + L * d < 0 ∧ 0 < c + U * d) ∨
      (0 < c + L * d ∧ c + U * d < 0) := by
  constructor
  · intro h
    exact (affineScalar_crossing_iff hd hLU).mp h.exists
  · intro h
    obtain ⟨t, ht⟩ := (affineScalar_crossing_iff hd hLU).mpr h
    exact ⟨t, ht, fun s hs => affineScalar_zero_unique hd hs.2.2 ht.2.2⟩

/-- The mod-two indicator of a strictly positive real value. -/
noncomputable def positiveBit (x : ℝ) : ZMod 2 := if 0 < x then 1 else 0

/-- Two nonzero values contribute an odd count exactly when their signs differ. -/
theorem positiveBit_add (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    positiveBit x + positiveBit y =
      if (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0) then 1 else 0 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;>
    rcases lt_or_gt_of_ne hy with hy | hy <;>
    simp [positiveBit, hx, hy, not_lt.mpr (le_of_lt hx),
      not_lt.mpr (le_of_lt hy), CharTwo.add_self_eq_zero]

/-- Positive endpoint count modulo two equals the indicator of an interior zero. -/
theorem affineScalar_endpoint_parity {c d L U : ℝ} (hd : d ≠ 0) (hLU : L < U)
    (hL : c + L * d ≠ 0) (hU : c + U * d ≠ 0) :
    positiveBit (c + L * d) + positiveBit (c + U * d) =
      if ∃ t, L < t ∧ t < U ∧ c + t * d = 0 then 1 else 0 := by
  simp only [positiveBit_add _ _ hL hU, affineScalar_crossing_iff hd hLU]

/-- Evaluate a scalar vertex coordinate on an affine coefficient line. -/
def sliceHeight {ι : Type*} [Fintype ι] (a w z : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, sliceCoeff a w t i * z i

theorem sliceHeight_eq_affine {ι : Type*} [Fintype ι] (a w z : ι → ℝ) (t : ℝ) :
    sliceHeight a w z t = (∑ i, a i * z i) + t * ∑ i, w i * z i := by
  simp only [sliceHeight, sliceCoeff, add_mul, Finset.sum_add_distrib,
    mul_assoc, Finset.mul_sum]

/-- Apply scalar parity to a height coordinate of a nonnegative coefficient
slice. Endpoint nonvanishing makes feasible zeros exactly interior zeros. -/
theorem sliceHeight_endpoint_parity {ι : Type*} [Fintype ι]
    (a w z : ι → ℝ) {L U : ℝ} (hLU : L < U)
    (hI : ∀ t, sliceFeasible a w t ↔ L ≤ t ∧ t ≤ U)
    (hd : ∑ i, w i * z i ≠ 0)
    (hL : sliceHeight a w z L ≠ 0) (hU : sliceHeight a w z U ≠ 0) :
    positiveBit (sliceHeight a w z L) + positiveBit (sliceHeight a w z U) =
      if ∃ t, sliceFeasible a w t ∧ sliceHeight a w z t = 0 then 1 else 0 := by
  have hex : (∃ t, L < t ∧ t < U ∧ sliceHeight a w z t = 0) ↔
      (∃ t, sliceFeasible a w t ∧ sliceHeight a w z t = 0) := by
    constructor
    · rintro ⟨t, htL, htU, ht⟩
      exact ⟨t, (hI t).mpr ⟨htL.le, htU.le⟩, ht⟩
    · rintro ⟨t, ht, hz⟩
      obtain ⟨htL, htU⟩ := (hI t).mp ht
      have hneL : L ≠ t := by rintro rfl; exact hL hz
      have hneU : t ≠ U := by rintro rfl; exact hU hz
      exact ⟨t, lt_of_le_of_ne htL hneL, lt_of_le_of_ne htU hneU, hz⟩
  simp_rw [sliceHeight_eq_affine] at hL hU hex ⊢
  rw [affineScalar_endpoint_parity hd hLU hL hU, hex]

end VCDimConvexBound
