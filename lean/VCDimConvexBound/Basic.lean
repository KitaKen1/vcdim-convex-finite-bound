import FormalConjecturesForMathlib.Combinatorics.Additive.VCDim
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Finite additive arrays and convex labels

These definitions implement the array-counting setup in section 1 of the
VCₙ argument in `FCreportv1.html`, exploration 30. The VCₙ predicate itself
is imported from the pinned Formal Conjectures library, not redefined here.
-/

namespace VCDimConvexBound

abbrev Grid (D m : ℕ) := Fin D → Fin m

abbrev Point (D : ℕ) := Fin D → ℝ

/-- The point associated with an index of an additive array. -/
def gridSum {D m : ℕ} {G : Type*} [AddCommMonoid G]
    (z : Fin D → Fin m → G) (i : Grid D m) : G :=
  ∑ k, z k (i k)

/-- A label set is realized by one additive array in a fixed set `C`. -/
def Realizes {D m : ℕ} {G : Type*} [AddCommMonoid G]
    (C : Set G) (S : Set (Grid D m)) : Prop :=
  ∃ z : Fin D → Fin m → G, ∀ i, gridSum z i ∈ C ↔ i ∈ S

/-- All labels realized by convex sets and additive arrays in ambient dimension `D`. -/
noncomputable def convexLabels (D m : ℕ) : Finset (Set (Grid D m)) := by
  classical
  exact Finset.univ.filter fun S =>
    ∃ C : Set (Point D), Convex ℝ C ∧ Realizes C S

@[simp] theorem mem_convexLabels {D m : ℕ} {S : Set (Grid D m)} :
    S ∈ convexLabels D m ↔ ∃ C : Set (Point D), Convex ℝ C ∧ Realizes C S := by
  classical
  simp [convexLabels]

@[simp] theorem card_grid (D m : ℕ) : Fintype.card (Grid D m) = m ^ D := by
  simp [Grid]

@[simp] theorem card_label_sets (D m : ℕ) :
    Fintype.card (Set (Grid D m)) = 2 ^ (m ^ D) := by
  simp

/-- The explicit bound proposed in the paper argument. -/
def bound (n : ℕ) : ℕ := 2 ^ (8 * (n + 2) ^ n) - 1

end VCDimConvexBound
