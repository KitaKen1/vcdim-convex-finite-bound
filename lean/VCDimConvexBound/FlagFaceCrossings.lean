import VCDimConvexBound.FlagSliceInterval

/-!
# Crossing indicators and actual deleted-column faces

Crossings use barycentric coefficients on a finite vertex set. Deleting a
vertex means restricting the coordinate and height rows to the remaining
columns. Inserting a zero coefficient identifies these crossings with the
corresponding boundary of the full coefficient simplex.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

/-- A barycentric solution of an arbitrary finite-column coordinate system. -/
def flagCrossingPoint {ρ ι : Type*} [Fintype ι] (X : Matrix ρ ι ℝ) (x : ι → ℝ) : Prop :=
  (∑ i, x i) = 1 ∧ X *ᵥ x = 0 ∧ ∀ i, 0 ≤ x i

/-- The indicator that the coordinate plane meets the coefficient simplex. -/
noncomputable def flagZeroBit {ρ ι : Type*} [Fintype ι] (X : Matrix ρ ι ℝ) : ZMod 2 :=
  if ∃ x, flagCrossingPoint X x then 1 else 0

/-- A crossing whose next coordinate is strictly positive. -/
def flagHasPositiveCrossing {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) : Prop :=
  ∃ x, flagCrossingPoint X x ∧ 0 < ∑ i, x i * z i

noncomputable def flagPositiveBit {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) : ZMod 2 :=
  if flagHasPositiveCrossing X z then 1 else 0

/-- A positive crossing on the boundary where the coefficient of p is zero. -/
def flagHasBoundaryCrossing {ρ ι : Type*} [Fintype ι]
    (X : Matrix ρ ι ℝ) (z : ι → ℝ) (p : ι) : Prop :=
  ∃ x, flagCrossingPoint X x ∧ x p = 0 ∧ 0 < ∑ i, x i * z i

/-- Inserting a zero coefficient preserves total mass. -/
theorem sum_insertNth_zero {k : ℕ} (p : Fin (k + 1)) (x : Fin k → ℝ) :
    ∑ i, Fin.insertNth p 0 x i = ∑ j, x j := by
  rw [Fin.sum_univ_succAbove _ p]
  simp

/-- Inserting a zero coefficient preserves every weighted scalar coordinate. -/
theorem sum_insertNth_zero_mul {k : ℕ} (p : Fin (k + 1))
    (x : Fin k → ℝ) (z : Fin (k + 1) → ℝ) :
    ∑ i, (Fin.insertNth p 0 x : Fin (k + 1) → ℝ) i * z i = ∑ j, x j * z (p.succAbove j) := by
  rw [Fin.sum_univ_succAbove _ p]
  simp

/-- A zero coefficient can be removed and then restored exactly. -/
theorem insertNth_zero_restrict {k : ℕ} (p : Fin (k + 1))
    (x : Fin (k + 1) → ℝ) (hp : x p = 0) :
    Fin.insertNth p 0 (fun j => x (p.succAbove j)) = x := by
  funext i
  refine Fin.succAboveCases p ?_ (fun j => ?_) i
  · simpa using hp.symm
  · simp

/-- The inserted coefficient vector has the same image under the coordinate matrix. -/
theorem mulVec_insertNth_zero {ρ : Type*} {k : ℕ}
    (X : Matrix ρ (Fin (k + 1)) ℝ) (p : Fin (k + 1)) (x : Fin k → ℝ) :
    X *ᵥ Fin.insertNth p 0 x = X.submatrix id p.succAbove *ᵥ x := by
  have h := mulVec_delete_zero X (Fin.insertNth p 0 x) p (by simp)
  simpa using h.symm

/-- Face feasibility is exactly full-simplex feasibility after zero insertion. -/
theorem flagCrossingPoint_insert_zero_iff {ρ : Type*} {k : ℕ}
    (X : Matrix ρ (Fin (k + 1)) ℝ) (p : Fin (k + 1)) (x : Fin k → ℝ) :
    flagCrossingPoint X (Fin.insertNth p 0 x) ↔
      flagCrossingPoint (X.submatrix id p.succAbove) x := by
  unfold flagCrossingPoint
  rw [sum_insertNth_zero, mulVec_insertNth_zero]
  constructor
  · rintro ⟨hm, hX, hnonneg⟩
    exact ⟨hm, hX, fun j => by simpa using hnonneg (p.succAbove j)⟩
  · rintro ⟨hm, hX, hnonneg⟩
    refine ⟨hm, hX, ?_⟩
    intro i
    refine Fin.succAboveCases p ?_ (fun j => ?_) i
    · simp
    · simpa using hnonneg j

/-- A positive crossing on a deleted-column face is precisely a boundary crossing. -/
theorem flagPositiveCrossing_face_iff {ρ : Type*} {k : ℕ}
    (X : Matrix ρ (Fin (k + 1)) ℝ) (z : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    flagHasPositiveCrossing (X.submatrix id p.succAbove) (fun j => z (p.succAbove j)) ↔
      flagHasBoundaryCrossing X z p := by
  constructor
  · rintro ⟨x, hx, hz⟩
    exact ⟨Fin.insertNth p 0 x, (flagCrossingPoint_insert_zero_iff X p x).mpr hx,
      by simp, by simpa only [sum_insertNth_zero_mul] using hz⟩
  · rintro ⟨x, hx, hp, hz⟩
    let y := fun j => x (p.succAbove j)
    have heq : Fin.insertNth p 0 y = x := insertNth_zero_restrict p x hp
    refine ⟨y, (flagCrossingPoint_insert_zero_iff X p y).mp (heq.symm ▸ hx), ?_⟩
    rw [← heq, sum_insertNth_zero_mul] at hz
    exact hz

/-- Zeroing one extra coordinate is the zero crossing of the row-augmented matrix. -/
theorem flagZeroBit_prepend {r n : ℕ} (X : Matrix (Fin r) (Fin n) ℝ) (z : Fin n → ℝ) :
    flagZeroBit (flagPrependRow z X) =
      if ∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) = 0 then 1 else 0 := by
  have heq (x : Fin n → ℝ) : flagPrependRow z X *ᵥ x = 0 ↔
      X *ᵥ x = 0 ∧ (∑ i, x i * z i) = 0 := by
    rw [flagPrependRow_mulVec]
    constructor
    · intro h
      refine ⟨funext fun i => congrFun h i.succ, ?_⟩
      have hh : (∑ i, z i * x i) = 0 := congrFun h 0
      simpa only [mul_comm] using hh
    · rintro ⟨hX, hz⟩
      have hz' : (∑ i, z i * x i) = 0 := by simpa only [mul_comm] using hz
      rw [hX, hz']
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
  have hiff : (∃ x, flagCrossingPoint (flagPrependRow z X) x) ↔
      (∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) = 0) := by
    simp only [flagCrossingPoint, heq]
    aesop
  unfold flagZeroBit
  rw [hiff]

end VCDimConvexBound
