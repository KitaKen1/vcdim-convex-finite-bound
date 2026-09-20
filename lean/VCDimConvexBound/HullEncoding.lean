import VCDimConvexBound.Basic
import Mathlib.Analysis.Convex.Independent

/-!
# Recover convex labels from an irredundant finite set

This implements the finite convex-hull reduction in section 4 of the paper
argument. Minimality removes redundant indices, including repeated points.
The ambient convex set need not be closed or bounded. No estimate on the
number of representatives is asserted here.
-/

namespace VCDimConvexBound

variable {ι : Type*} {D : ℕ}

/-- The convex hull of the points indexed by a finite set. -/
def indexedHull (q : ι → Point D) (V : Finset ι) : Set (Point D) :=
  convexHull ℝ (q '' (V : Set ι))

/-- No selected point is in the convex hull of the other selected indices. -/
def ConvexIndependentOn [DecidableEq ι] (q : ι → Point D) (V : Finset ι) : Prop :=
  ∀ i ∈ V, q i ∉ indexedHull q (V.erase i)

theorem indexedHull_mono (q : ι → Point D) {V W : Finset ι} (h : V ⊆ W) :
    indexedHull q V ⊆ indexedHull q W :=
  convexHull_mono (Set.image_mono h)

theorem mem_indexedHull (q : ι → Point D) {V : Finset ι} {i : ι} (hi : i ∈ V) :
    q i ∈ indexedHull q V :=
  subset_convexHull ℝ _ ⟨i, hi, rfl⟩

/-- Removing a redundant index does not change the hull. -/
theorem indexedHull_erase_eq [DecidableEq ι] (q : ι → Point D) (V : Finset ι) (i : ι)
    (hi : q i ∈ indexedHull q (V.erase i)) :
    indexedHull q (V.erase i) = indexedHull q V := by
  apply Set.Subset.antisymm (indexedHull_mono q (Finset.erase_subset _ _))
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨j, hj, rfl⟩
  by_cases hji : j = i
  · subst j
    exact hi
  · exact mem_indexedHull q (Finset.mem_erase.mpr ⟨hji, hj⟩)

/-- A smallest subset of `E` with the same hull exists, including when `E` is empty. -/
theorem exists_minimal_generators (q : ι → Point D) (E : Finset ι) :
    ∃ V : Finset ι, V ⊆ E ∧ indexedHull q V = indexedHull q E ∧
      ∀ W : Finset ι, W ⊆ E → indexedHull q W = indexedHull q E → V.card ≤ W.card := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ V : Finset ι, V ⊆ E ∧ indexedHull q V = indexedHull q E ∧ V.card = k
  have hex : ∃ k, P k := ⟨E.card, E, Finset.Subset.refl E, rfl, rfl⟩
  obtain ⟨V, hVE, hHull, hcard⟩ := Nat.find_spec hex
  refine ⟨V, hVE, hHull, ?_⟩
  intro W hWE hW
  rw [hcard]
  exact Nat.find_min' hex ⟨W, hWE, hW, rfl⟩

/-- Minimal generators are convex independent as an indexed family. -/
theorem exists_convexIndependent_generators [DecidableEq ι] (q : ι → Point D) (E : Finset ι) :
    ∃ V : Finset ι, V ⊆ E ∧ indexedHull q V = indexedHull q E ∧
      ConvexIndependentOn q V := by
  obtain ⟨V, hVE, hHull, hmin⟩ := exists_minimal_generators q E
  refine ⟨V, hVE, hHull, ?_⟩
  intro i hi hredundant
  have hle := hmin (V.erase i) ((Finset.erase_subset _ _).trans hVE)
    ((indexedHull_erase_eq q V i hredundant).trans hHull)
  exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hi)) hle

/-- Connect the finite erase formulation to mathlib's standard predicate. -/
theorem ConvexIndependentOn.convexIndependent [DecidableEq ι]
    {q : ι → Point D} {V : Finset ι} (hV : ConvexIndependentOn q V) :
    ConvexIndependent ℝ (fun i : V => q i) := by
  intro s i hi
  by_contra his
  apply hV i i.property
  apply convexHull_mono _ hi
  rintro _ ⟨j, hjs, rfl⟩
  refine ⟨j.val, Finset.mem_erase.mpr ⟨?_, j.property⟩, rfl⟩
  intro hji
  have h : j = i := Subtype.ext hji
  exact his (h ▸ hjs)

/-- Convex independence of an indexed family excludes repeated points. -/
theorem ConvexIndependentOn.injOn [DecidableEq ι] {q : ι → Point D} {V : Finset ι}
    (hV : ConvexIndependentOn q V) : Set.InjOn q (V : Set ι) := by
  intro i hi j hj hij
  by_contra hne
  apply hV i hi
  rw [hij]
  exact mem_indexedHull q (Finset.mem_erase.mpr ⟨Ne.symm hne, hj⟩)

/-- The positive indices of a finite configuration. -/
noncomputable def positiveIndices [Fintype ι] (q : ι → Point D) (C : Set (Point D)) :
    Finset ι := by
  classical
  exact Finset.univ.filter fun i => q i ∈ C

@[simp] theorem mem_positiveIndices [Fintype ι] (q : ι → Point D)
    (C : Set (Point D)) (i : ι) : i ∈ positiveIndices q C ↔ q i ∈ C := by
  classical
  simp [positiveIndices]

/-- Taking the hull of all positive points preserves the label of every indexed point. -/
theorem mem_indexedHull_positive_iff [Fintype ι] (q : ι → Point D)
    (C : Set (Point D)) (hC : Convex ℝ C) (i : ι) :
    q i ∈ indexedHull q (positiveIndices q C) ↔ q i ∈ C := by
  constructor
  · apply convexHull_min _ hC
    rintro _ ⟨j, hj, rfl⟩
    exact (mem_positiveIndices q C j).mp hj
  · intro hi
    exact mem_indexedHull q ((mem_positiveIndices q C i).mpr hi)

/-- Every convex label has distinct, convex-independent representatives.
The later geometric argument must supply a bound on `V.card`. -/
theorem exists_label_generators [DecidableEq ι] [Fintype ι] (q : ι → Point D)
    (C : Set (Point D)) (hC : Convex ℝ C) :
    ∃ V : Finset ι, V ⊆ positiveIndices q C ∧ ConvexIndependentOn q V ∧
      Set.InjOn q (V : Set ι) ∧ ∀ i, q i ∈ C ↔ q i ∈ indexedHull q V := by
  obtain ⟨V, hVE, hHull, hind⟩ :=
    exists_convexIndependent_generators q (positiveIndices q C)
  refine ⟨V, hVE, hind, hind.injOn, ?_⟩
  intro i
  rw [hHull]
  exact (mem_indexedHull_positive_iff q C hC i).symm

/-- Connect the finite-hull reduction to the label sets counted in `Basic`.
There is no bound on `V.card` yet. -/
theorem exists_hull_encoding_of_mem_convexLabels {m : ℕ} {S : Set (Grid D m)}
    (hS : S ∈ convexLabels D m) :
    ∃ (z : Fin D → Fin m → Point D) (V : Finset (Grid D m)),
      ConvexIndependentOn (gridSum z) V ∧
      ConvexIndependent ℝ (fun i : V => gridSum z i) ∧
      Set.InjOn (gridSum z) (V : Set (Grid D m)) ∧
      (V : Set (Grid D m)) ⊆ S ∧
      S = {i | gridSum z i ∈ indexedHull (gridSum z) V} := by
  classical
  obtain ⟨C, hC, z, hz⟩ := mem_convexLabels.mp hS
  obtain ⟨V, hVE, hind, hinj, hlabels⟩ := exists_label_generators (gridSum z) C hC
  refine ⟨z, V, hind, hind.convexIndependent, hinj, ?_, ?_⟩
  · intro i hi
    exact (hz i).mp ((mem_positiveIndices (gridSum z) C i).mp (hVE hi))
  · ext i
    exact (hz i).symm.trans (hlabels i)

end VCDimConvexBound
