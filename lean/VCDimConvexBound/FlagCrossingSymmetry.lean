import VCDimConvexBound.FlagFaceCrossings

/-!
# Invariance and the antipodal crossing identity

Crossing indicators are independent of how finite vertices are numbered.
For a simplex with a unique coordinate crossing and nonzero next height,
its zero-crossing indicator is the sum of positive-crossing indicators for
itself and its global negative. This is the second local identity needed
for the hemisphere recurrence; no global odd-map obstruction is claimed.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

/-- Reindexing vertices preserves the coordinate image of reindexed coefficients. -/
theorem flag_mulVec_reindex {ρ ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ρ ι ℝ) (e : κ ≃ ι) (x : ι → ℝ) :
    X.submatrix id e *ᵥ (x ∘ e) = X *ᵥ x := by
  funext r
  exact e.sum_comp (fun i => X r i * x i)

/-- Feasibility depends on the vertex set, not its numbering. -/
theorem flagCrossingPoint_reindex_iff {ρ ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ρ ι ℝ) (e : κ ≃ ι) (x : ι → ℝ) :
    flagCrossingPoint (X.submatrix id e) (x ∘ e) ↔ flagCrossingPoint X x := by
  unfold flagCrossingPoint
  rw [flag_mulVec_reindex]
  have hs : ∑ i, (x ∘ e) i = ∑ i, x i := e.sum_comp x
  rw [hs]
  constructor
  · rintro ⟨hm, hX, hx⟩
    exact ⟨hm, hX, fun i => by simpa using hx (e.symm i)⟩
  · rintro ⟨hm, hX, hx⟩
    exact ⟨hm, hX, fun i => hx (e i)⟩

/-- Zero-crossing indicators are invariant under any vertex equivalence. -/
theorem flagZeroBit_reindex {ρ ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ρ ι ℝ) (e : κ ≃ ι) :
    flagZeroBit (X.submatrix id e) = flagZeroBit X := by
  have hiff : (∃ y, flagCrossingPoint (X.submatrix id e) y) ↔
      (∃ x, flagCrossingPoint X x) := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ e.symm, (flagCrossingPoint_reindex_iff X e _).mp ?_⟩
      simpa only [Function.comp_def, Equiv.symm_apply_apply] using hy
    · rintro ⟨x, hx⟩
      exact ⟨x ∘ e, (flagCrossingPoint_reindex_iff X e x).mpr hx⟩
  simp only [flagZeroBit, hiff]

/-- Positive-crossing indicators are invariant under simultaneous vertex reindexing. -/
theorem flagPositiveBit_reindex {ρ ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) (e : κ ≃ ι) :
    flagPositiveBit (X.submatrix id e) (z ∘ e) = flagPositiveBit X z := by
  have hiff : flagHasPositiveCrossing (X.submatrix id e) (z ∘ e) ↔
      flagHasPositiveCrossing X z := by
    constructor
    · rintro ⟨y, hy, hz⟩
      refine ⟨y ∘ e.symm, (flagCrossingPoint_reindex_iff X e _).mp ?_, ?_⟩
      · simpa only [Function.comp_def, Equiv.symm_apply_apply] using hy
      · have hs := e.sum_comp (fun i => (y ∘ e.symm) i * z i)
        rw [← hs]
        simpa only [Function.comp_def, Equiv.symm_apply_apply] using hz
    · rintro ⟨x, hx, hz⟩
      refine ⟨x ∘ e, (flagCrossingPoint_reindex_iff X e x).mpr hx, ?_⟩
      have hs := e.sum_comp (fun i => x i * z i)
      exact hs.symm ▸ hz
  simp only [flagPositiveBit, hiff]

/-- Negating every vertex image leaves the zero-coordinate equations unchanged. -/
theorem flagCrossingPoint_neg_iff {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (x : ι → ℝ) :
    flagCrossingPoint (-X) x ↔ flagCrossingPoint X x := by
  simp [flagCrossingPoint, Matrix.neg_mulVec]

theorem flagZeroBit_neg {ρ ι : Type*} [Fintype ι] (X : Matrix ρ ι ℝ) :
    flagZeroBit (-X) = flagZeroBit X := by
  simp only [flagZeroBit, flagCrossingPoint_neg_iff]

/-- Positive height on the antipodal simplex is negative height on the original. -/
theorem flagPositiveCrossing_neg_iff {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) :
    flagHasPositiveCrossing (-X) (-z) ↔
      ∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) < 0 := by
  simp [flagHasPositiveCrossing, flagCrossingPoint_neg_iff, Finset.sum_neg_distrib]

/-- A nonsingular mass-augmented square system has at most one crossing. -/
theorem flagCrossingPoint_unique {k : ℕ}
    (X : Matrix (Fin k) (Fin (k + 1)) ℝ)
    (hdet : (flagPrependRow (fun _ => 1) X).det ≠ 0)
    (x y : Fin (k + 1) → ℝ) (hx : flagCrossingPoint X x) (hy : flagCrossingPoint X y) :
    x = y := by
  have hu : IsUnit (flagPrependRow (fun _ => 1) X) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  simp only [flagPrependRow_mulVec, one_mul, hx.1, hy.1, hx.2.1, hy.2.1]

/-- A nonsingular height-augmented square system forbids a zero-height crossing. -/
theorem flagCrossingPoint_height_ne_zero {k : ℕ}
    (X : Matrix (Fin k) (Fin (k + 1)) ℝ) (z : Fin (k + 1) → ℝ)
    (hdet : (flagPrependRow z X).det ≠ 0)
    (x : Fin (k + 1) → ℝ) (hx : flagCrossingPoint X x) :
    ∑ i, x i * z i ≠ 0 := by
  intro hz
  have hu : IsUnit (flagPrependRow z X) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have heq : x = 0 := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr hu
    have hz' : (∑ i, z i * x i) = 0 := by simpa only [mul_comm] using hz
    rw [Matrix.mulVec_zero, flagPrependRow_mulVec, hz', hx.2.1]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hm := hx.1
  simp [heq] at hm

/-- The local antipodal identity q = alpha + A*alpha, including no-crossing cases. -/
theorem flag_antipodal_crossing_parity {k : ℕ}
    (X : Matrix (Fin k) (Fin (k + 1)) ℝ) (z : Fin (k + 1) → ℝ)
    (hmass : (flagPrependRow (fun _ => 1) X).det ≠ 0)
    (hheight : (flagPrependRow z X).det ≠ 0) :
    flagZeroBit X = flagPositiveBit X z + flagPositiveBit (-X) (-z) := by
  by_cases hfeas : ∃ x, flagCrossingPoint X x
  · obtain ⟨x, hx⟩ := hfeas
    have hp : flagHasPositiveCrossing X z ↔ 0 < ∑ i, x i * z i := by
      constructor
      · rintro ⟨y, hy, hz⟩
        have heq := flagCrossingPoint_unique X hmass y x hy hx
        simpa only [heq] using hz
      · intro hz
        exact ⟨x, hx, hz⟩
    have hn : flagHasPositiveCrossing (-X) (-z) ↔ (∑ i, x i * z i) < 0 := by
      rw [flagPositiveCrossing_neg_iff]
      constructor
      · rintro ⟨y, hy, hz⟩
        have heq := flagCrossingPoint_unique X hmass y x hy hx
        simpa only [heq] using hz
      · intro hz
        exact ⟨x, hx, hz⟩
    have hz := flagCrossingPoint_height_ne_zero X z hheight x hx
    have he : ∃ x, flagCrossingPoint X x := ⟨x, hx⟩
    simp only [flagZeroBit, if_pos he, flagPositiveBit, hp, hn]
    rcases lt_or_gt_of_ne hz with hz | hz <;> simp [hz, not_lt.mpr (le_of_lt hz)]
  · have hp : ¬ flagHasPositiveCrossing X z := fun ⟨x, hx, _⟩ => hfeas ⟨x, hx⟩
    have hn : ¬ flagHasPositiveCrossing (-X) (-z) := by
      rw [flagPositiveCrossing_neg_iff]
      exact fun ⟨x, hx, _⟩ => hfeas ⟨x, hx⟩
    simp [flagZeroBit, flagPositiveBit, hfeas, hp, hn]

/-- With one vertex and no coordinate equations, the base crossing count is one. -/
theorem flagZeroBit_single_vertex (X : Matrix (Fin 0) (Fin 1) ℝ) :
    flagZeroBit X = 1 := by
  have h : ∃ x, flagCrossingPoint X x := by
    refine ⟨fun _ => 1, ?_, ?_, ?_⟩
    · simp
    · funext i
      exact Fin.elim0 i
    · intro i
      exact zero_le_one
  exact if_pos h

end VCDimConvexBound
