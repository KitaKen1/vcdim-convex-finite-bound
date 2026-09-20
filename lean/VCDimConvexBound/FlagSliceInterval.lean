import VCDimConvexBound.FlagSliceMatrix

/-!
# From coordinate matrices to the two-endpoint parity identity

The affine-line and nondegeneracy hypotheses are now derived from explicit
minor conditions on the original coordinate constraints. The remaining
local cochain step is to identify the two endpoint terms with the sum over
all abstract boundary faces. General-position perturbation is also pending.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

/-- A nonnegative mass-one solution of the coordinate equations. -/
def flagSlicePoint {r : ℕ} (X : Matrix (Fin r) (Fin (r + 2)) ℝ)
    (x : Fin (r + 2) → ℝ) : Prop :=
  (∑ i, x i) = 1 ∧ X *ᵥ x = 0 ∧ ∀ i, 0 ≤ x i

/-- The full interval description for an actual nonempty coordinate slice.
All genericity hypotheses of the earlier scalar lemmas follow from minors. -/
theorem exists_flagSlice_interval {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hG : FlagSliceGeneric X z) (hfeas : ∃ x, flagSlicePoint X x) :
    ∃ a w : Fin (r + 2) → ℝ, ∃ L U : ℝ, ∃ p n : Fin (r + 2),
      L < U ∧ p ≠ n ∧
      (∀ x, ((∑ i, x i) = 1 ∧ X *ᵥ x = 0) ↔ ∃ t : ℝ, x = sliceCoeff a w t) ∧
      (∀ t, sliceFeasible a w t ↔ L ≤ t ∧ t ≤ U) ∧
      (∀ i, sliceCoeff a w L i = 0 ↔ i = p) ∧
      (∀ i, sliceCoeff a w U i = 0 ↔ i = n) ∧
      (∀ t, L < t → t < U → ∀ i, 0 < sliceCoeff a w t i) ∧
      (∀ t, (sliceFeasible a w t ∧ ∃ i, sliceCoeff a w t i = 0) ↔ t = L ∨ t = U) ∧
      (∑ i, w i * z i) ≠ 0 ∧
      sliceHeight a w z L ≠ 0 ∧ sliceHeight a w z U ≠ 0 := by
  obtain ⟨a, w, _, _, hw, _, hne, hwi, hNo, hz, hline⟩ := exists_flagSlice_line X z hG
  have htfeas : ∃ t, sliceFeasible a w t := by
    obtain ⟨x, hmass, hX, hnonneg⟩ := hfeas
    obtain ⟨t, rfl⟩ := (hline x).mp ⟨hmass, hX⟩
    exact ⟨t, hnonneg⟩
  obtain ⟨L, U, p, n, hLU, hpn, _, _, hI, hLp, hUn, hint, hboundary⟩ :=
    exists_generic_slice_endpoints a w hw hne hwi hNo htfeas
  refine ⟨a, w, L, U, p, n, hLU, hpn, hline, hI, hLp, hUn, hint, hboundary, hz, ?_, ?_⟩
  · have ht := (hline (sliceCoeff a w L)).mpr ⟨L, rfl⟩
    exact flagSlice_boundary_height_ne_zero X z hG.height_minors _ ht.1 ht.2 p
      ((hLp p).mpr rfl)
  · have ht := (hline (sliceCoeff a w U)).mpr ⟨U, rfl⟩
    exact flagSlice_boundary_height_ne_zero X z hG.height_minors _ ht.1 ht.2 n
      ((hUn n).mpr rfl)

/-- The actual coordinate slice has two distinct boundary points, each with
one zero coefficient, whose positive-height count detects a height-zero
solution modulo two. The boundary-face indexing step is not asserted here. -/
theorem exists_flagSlice_endpoint_parity {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hG : FlagSliceGeneric X z) (hfeas : ∃ x, flagSlicePoint X x) :
    ∃ l u : Fin (r + 2) → ℝ, ∃ p n : Fin (r + 2),
      flagSlicePoint X l ∧ flagSlicePoint X u ∧ l ≠ u ∧ p ≠ n ∧
      (∀ i, l i = 0 ↔ i = p) ∧ (∀ i, u i = 0 ↔ i = n) ∧
      positiveBit (∑ i, l i * z i) + positiveBit (∑ i, u i * z i) =
        if ∃ x, flagSlicePoint X x ∧ (∑ i, x i * z i) = 0 then 1 else 0 := by
  obtain ⟨a, w, L, U, p, n, hLU, hpn, hline, hI, hLp, hUn, _, _, hd, hL, hU⟩ :=
    exists_flagSlice_interval X z hG hfeas
  have hLl := (hline (sliceCoeff a w L)).mpr ⟨L, rfl⟩
  have hUl := (hline (sliceCoeff a w U)).mpr ⟨U, rfl⟩
  have hl : flagSlicePoint X (sliceCoeff a w L) :=
    ⟨hLl.1, hLl.2, (hI L).mpr ⟨le_rfl, hLU.le⟩⟩
  have hu : flagSlicePoint X (sliceCoeff a w U) :=
    ⟨hUl.1, hUl.2, (hI U).mpr ⟨hLU.le, le_rfl⟩⟩
  have hne : sliceCoeff a w L ≠ sliceCoeff a w U := by
    intro heq
    have hzL := (hLp p).mpr rfl
    rw [heq] at hzL
    exact hpn ((hUn p).mp hzL)
  refine ⟨sliceCoeff a w L, sliceCoeff a w U, p, n, hl, hu, hne, hpn, hLp, hUn, ?_⟩
  have hex : (∃ t, sliceFeasible a w t ∧ sliceHeight a w z t = 0) ↔
      (∃ x, flagSlicePoint X x ∧ (∑ i, x i * z i) = 0) := by
    constructor
    · rintro ⟨t, ht, hz⟩
      have heq := (hline (sliceCoeff a w t)).mpr ⟨t, rfl⟩
      exact ⟨sliceCoeff a w t, ⟨heq.1, heq.2, ht⟩, hz⟩
    · rintro ⟨x, hx, hz⟩
      obtain ⟨t, rfl⟩ := (hline x).mp ⟨hx.1, hx.2.1⟩
      exact ⟨t, hx.2.2, hz⟩
  change positiveBit (sliceHeight a w z L) + positiveBit (sliceHeight a w z U) = _
  rw [sliceHeight_endpoint_parity a w z hLU hI hd hL hU, hex]

end VCDimConvexBound
