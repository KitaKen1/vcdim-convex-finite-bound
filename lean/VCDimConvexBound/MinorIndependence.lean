import VCDimConvexBound.CramerSigns
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# What all minor signs remember about linear systems

Independent columns admit a nonsingular row restriction. Equal signs for all
row-subset minors therefore preserve independence and membership in the span
of any independent subfamily. This works for rectangular and rank-deficient
ambient configurations; the nonsingular matrix is selected locally.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

theorem exists_nonsingular_row_restriction {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (A : Matrix ρ κ ℝ) (hA : LinearIndependent ℝ A.col) :
    ∃ r : κ ↪ ρ, (A.submatrix r id).det ≠ 0 := by
  classical
  obtain ⟨η, c, hc, hspan, hli⟩ := exists_linearIndependent' ℝ A.row
  let : Fintype η := Fintype.ofInjective c hc
  have hcols : A.rank = Fintype.card κ := by
    have ht : LinearIndependent ℝ A.transpose.row := hA
    simpa only [Matrix.rank_transpose] using ht.rank_matrix
  have hcard : Fintype.card η = Fintype.card κ := by
    calc
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range (A.row ∘ c))) :=
        linearIndependent_iff_card_eq_finrank_span.mp hli
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) := by rw [hspan]
      _ = A.rank := A.rank_eq_finrank_span_row.symm
      _ = _ := hcols
  let e : κ ≃ η := Fintype.equivOfCardEq hcard.symm
  let r : κ ↪ ρ := ⟨c ∘ e, hc.comp e.injective⟩
  have hr : LinearIndependent ℝ (A.submatrix r id).row := by
    change LinearIndependent ℝ (fun i j => A (c (e i)) j)
    simpa [Matrix.row, Function.comp_def] using! hli.comp e e.injective
  exact ⟨r, isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hr))⟩

/-- Equality of signs of every row-subset minor, allowing arbitrary column choices. -/
def SameMinorSigns {ρ ι : Type*} (A B : Matrix ρ ι ℝ) : Prop := by
  classical
  exact ∀ (R : Finset ρ) (c : R → ι),
    signCode (A.submatrix Subtype.val c).det = signCode (B.submatrix Subtype.val c).det

theorem SameMinorSigns.symm {ρ ι : Type*} {A B : Matrix ρ ι ℝ}
    (h : SameMinorSigns A B) : SameMinorSigns B A := fun R c => (h R c).symm

/-- The row-subset encoding includes any injectively indexed square row restriction. -/
theorem SameMinorSigns.det_submatrix {ρ ι κ : Type*} [Fintype κ] [DecidableEq κ]
    {A B : Matrix ρ ι ℝ} (h : SameMinorSigns A B) (r : κ ↪ ρ) (c : κ → ι) :
    signCode (A.submatrix r c).det = signCode (B.submatrix r c).det := by
  classical
  let R : Finset ρ := Finset.univ.map r
  let f : κ → R := fun i => ⟨r i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact r.injective (congrArg Subtype.val hij)
    · intro j
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp j.property
      exact ⟨i, Subtype.ext hi⟩
  let e : κ ≃ R := Equiv.ofBijective f hf
  have he : ∀ i, (e i).val = r i := fun _ => rfl
  have hd (M : Matrix ρ ι ℝ) :
      (M.submatrix r c).det = (M.submatrix Subtype.val (c ∘ e.symm)).det := by
    rw [← Matrix.det_submatrix_equiv_self e (M.submatrix Subtype.val (c ∘ e.symm))]
    congr 1
    ext i j
    simp [Matrix.submatrix, he]
  rw [hd A, hd B]
  exact h R (c ∘ e.symm)

/-- Independent columns stay independent when all minor signs are preserved. -/
theorem SameMinorSigns.linearIndependent {ρ ι κ : Type*} [Fintype ρ] [Fintype κ]
    {A B : Matrix ρ ι ℝ} (h : SameMinorSigns A B) (c : κ → ι)
    (hA : LinearIndependent ℝ (fun i => A.col (c i))) :
    LinearIndependent ℝ (fun i => B.col (c i)) := by
  classical
  obtain ⟨r, hr⟩ := exists_nonsingular_row_restriction (A.submatrix id c) hA
  have hr' : (A.submatrix r c).det ≠ 0 := by simpa using hr
  have hb : (B.submatrix r c).det ≠ 0 := fun hb =>
    hr' (((signCode_eq_iff _ _).mp (h.det_submatrix r c)).2.mpr hb)
  have hi := Matrix.linearIndependent_cols_of_det_ne_zero hb
  rw [linearIndependent_iff'] at hi ⊢
  intro s w hw
  apply hi s w
  funext i
  simpa [Matrix.col, Matrix.submatrix, Finset.sum_apply] using congrFun hw (r i)

theorem SameMinorSigns.linearIndependent_iff {ρ ι κ : Type*} [Fintype ρ] [Fintype κ]
    {A B : Matrix ρ ι ℝ} (h : SameMinorSigns A B) (c : κ → ι) :
    LinearIndependent ℝ (fun i => A.col (c i)) ↔
      LinearIndependent ℝ (fun i => B.col (c i)) :=
  ⟨h.linearIndependent c, h.symm.linearIndependent c⟩

/-- All minors, including the smaller ones, preserve span membership on independent supports. -/
theorem SameMinorSigns.mem_span_iff {ρ ι κ : Type*} [Fintype ρ] [Fintype κ]
    {A B : Matrix ρ ι ℝ} (h : SameMinorSigns A B) (c : κ → ι)
    (hA : LinearIndependent ℝ (fun j => A.col (c j))) (i : ι) :
    A.col i ∈ Submodule.span ℝ (Set.range (fun j => A.col (c j))) ↔
      B.col i ∈ Submodule.span ℝ (Set.range (fun j => B.col (c j))) := by
  have hB := h.linearIndependent c hA
  have he := h.linearIndependent_iff (fun j : Option κ => j.elim i c)
  apply not_iff_not.mp
  simpa [linearIndependent_option, Function.comp_def, hA, hB] using he

end VCDimConvexBound
