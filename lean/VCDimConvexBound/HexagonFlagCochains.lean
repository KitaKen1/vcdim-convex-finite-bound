import VCDimConvexBound.HexagonFaceEnumeration
import Mathlib.Data.Fin.Rev

/-!
# Coordinate-crossing cochains on actual hexagon faces

Coordinates are stored as a sequence. The first k rows are written in
reverse order so adding the next coordinate is exactly row prepending.
This is the same coordinate flag, with no change to the zero equations.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

def hexFlagMatrix {r : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    (f : Finset (HexVertex r)) : Matrix (Fin k) f ℝ :=
  Matrix.of (fun i v => p v.val i.rev.val)

noncomputable def hexFlagZero {r : ℕ} (p : HexVertex r → ℕ → ℝ)
    (k : ℕ) : HexModTwoChain r := fun f => flagZeroBit (hexFlagMatrix p k f)

noncomputable def hexFlagPositive {r : ℕ} (p : HexVertex r → ℕ → ℝ)
    (k : ℕ) : HexModTwoChain r :=
  fun f => flagPositiveBit (hexFlagMatrix p k f) (fun v => p v.val k)

/-- The matrix whose columns are any chosen listing of the actual face. -/
def hexFlagEnumMatrix {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) : Matrix (Fin k) (Fin n) ℝ :=
  (hexFlagMatrix p k f).submatrix id e

theorem hexFlagZero_eq_enumeration {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    (f : Finset (HexVertex r)) (e : Fin n ≃ f) :
    hexFlagZero p k f = flagZeroBit (hexFlagEnumMatrix p k e) :=
  (flagZeroBit_reindex (hexFlagMatrix p k f) e).symm

theorem hexFlagPositive_eq_enumeration {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    (f : Finset (HexVertex r)) (e : Fin n ≃ f) :
    hexFlagPositive p k f =
      flagPositiveBit (hexFlagEnumMatrix p k e) (fun j => p (e j).val k) :=
  (flagPositiveBit_reindex (hexFlagMatrix p k f) (fun v => p v.val k) e).symm

/-- Adding the next flag coordinate is row prepending in reverse row order. -/
theorem hexFlagEnumMatrix_succ {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) :
    hexFlagEnumMatrix p (k + 1) e =
      flagPrependRow (fun j => p (e j).val k) (hexFlagEnumMatrix p k e) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [hexFlagEnumMatrix, hexFlagMatrix, flagPrependRow]
  · simp [hexFlagEnumMatrix, hexFlagMatrix, flagPrependRow]

/-- Removing a column is precisely the matrix of the vertex-deleted face. -/
theorem hexFlagEnumMatrix_erase {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    {f : Finset (HexVertex r)} (e : Fin (n + 1) ≃ f) (i : Fin (n + 1)) :
    hexFlagEnumMatrix p k (hexFaceEraseEnumeration e i) =
      (hexFlagEnumMatrix p k e).submatrix id i.succAbove := rfl

theorem hexFlagPositive_erase {r n : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    {f : Finset (HexVertex r)} (e : Fin (n + 1) ≃ f) (i : Fin (n + 1)) :
    hexFlagPositive p k (f.erase (e i).val) =
      flagPositiveBit ((hexFlagEnumMatrix p k e).submatrix id i.succAbove)
        (fun j => p (e (i.succAbove j)).val k) := by
  rw [hexFlagPositive_eq_enumeration p k _ (hexFaceEraseEnumeration e i)]
  rfl

/-- Under odd vertex data, the actual antipodal face has the negative matrix. -/
theorem hexFlagPositive_antipodal {r : ℕ} (p : HexVertex r → ℕ → ℝ)
    (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j)
    (k : ℕ) (f : Finset (HexVertex r)) :
    hexFlagPositive p k (f.image hexVertexOpposite) =
      flagPositiveBit (-hexFlagMatrix p k f) (fun v => -p v.val k) := by
  unfold hexFlagPositive
  rw [← flagPositiveBit_reindex _ _ (hexFaceAntipodalEquiv f)]
  congr 1
  · ext i v
    exact hp v.val i.rev.val
  · funext v
    exact hp v.val k

/-- One vertex always meets the flag with zero coordinate equations. -/
theorem hexFlagZero_vertex {r : ℕ} (p : HexVertex r → ℕ → ℝ) (v : HexVertex r) :
    hexFlagZero p 0 {v} = 1 := by
  rw [hexFlagZero_eq_enumeration p 0 _ (hexFaceEnumeration (n := 1) {v} (by simp))]
  exact flagZeroBit_single_vertex _

/-- Nonzero q is an actual barycentric zero of all the first k coordinates. -/
theorem hexFlagZero_ne_zero_iff {r : ℕ} (p : HexVertex r → ℕ → ℝ) (k : ℕ)
    (f : Finset (HexVertex r)) :
    hexFlagZero p k f ≠ 0 ↔ ∃ x : f → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧
        ∀ j : Fin k, (∑ v, x v * p v.val j.val) = 0 := by
  classical
  have he (x : f → ℝ) : hexFlagMatrix p k f *ᵥ x = 0 ↔
      ∀ j : Fin k, (∑ v, x v * p v.val j.val) = 0 := by
    constructor
    · intro h j
      have h' := congrFun h j.rev
      change (∑ v, p v.val j.rev.rev.val * x v) = 0 at h'
      rw [Fin.rev_rev] at h'
      simpa only [mul_comm] using h'
    · intro h
      funext i
      change (∑ v, p v.val i.rev.val * x v) = 0
      simpa only [mul_comm] using h i.rev
  simp only [hexFlagZero, flagZeroBit, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not, flagCrossingPoint, he]
  aesop

end VCDimConvexBound
