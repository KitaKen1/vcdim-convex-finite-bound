import VCDimConvexBound.MinorHullRecovery
import VCDimConvexBound.MinorSignPatterns
import VCDimConvexBound.SparseGenerators

/-!
# Count convex labels by minor signs and representative subsets

P5 makes the encoding injective. The sparse version explicitly retains
`SanyalBoxObstruction`; no geometric input is declared as an axiom.
-/

namespace VCDimConvexBound

/-- The minor sign vector of an additive array. -/
noncomputable def arrayMinorSigns {D m : ℕ} (z : Fin D → Fin m → Point D) :
    MinorIndex D m → Fin 3 :=
  fun j => signCode (MvPolynomial.eval (arrayAssignment z) (minorPolynomial j))

theorem arrayMinorSigns_mem {D m : ℕ} (z : Fin D → Fin m → Point D) :
    arrayMinorSigns z ∈ minorSignPatterns D m := by
  classical
  simp only [minorSignPatterns, ternaryPatterns, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨arrayAssignment z, fun _ => rfl⟩

/-- Any family of representative subsets covering all labels gives a product bound. -/
theorem card_convexLabels_le_signs_mul_generators {D m : ℕ}
    (G : Finset (Finset (Grid D m)))
    (hgen : ∀ S ∈ convexLabels D m,
      ∃ (z : Fin D → Fin m → Point D) (V : Finset (Grid D m)),
        V ∈ G ∧ ∀ i, i ∈ S ↔ gridSum z i ∈ indexedHull (gridSum z) V) :
    (convexLabels D m).card ≤ (minorSignPatterns D m).card * G.card := by
  classical
  choose z V hV hlabels using fun S : ↑(convexLabels D m) => hgen S S.property
  let encode : ↑(convexLabels D m) → ↑(minorSignPatterns D m) × ↑G :=
    fun S => (⟨arrayMinorSigns (z S), arrayMinorSigns_mem (z S)⟩, ⟨V S, hV S⟩)
  have hinj : Function.Injective encode := by
    intro S T he
    have hs : arrayMinorSigns (z S) = arrayMinorSigns (z T) :=
      congrArg (fun e => e.1.val) he
    have hv : V S = V T := congrArg (fun e => e.2.val) he
    apply Subtype.ext
    ext i
    rw [hlabels S i, hlabels T i, ← hv]
    exact same_signs_same_hull_membership (z S) (z T) (fun j => congrFun hs j) (V S) i
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective encode hinj

/-- Candidate representative subsets of density strictly less than one sixteenth. -/
noncomputable def sparseSubsets (ι : Type*) [Fintype ι] : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun V => 16 * V.card < Fintype.card ι

@[simp] theorem mem_sparseSubsets {ι : Type*} [Fintype ι] (V : Finset ι) :
    V ∈ sparseSubsets ι ↔ 16 * V.card < Fintype.card ι := by
  classical
  simp [sparseSubsets]

/-- P4 and P5: the number of convex labels is at most the product of the two code counts. -/
theorem card_convexLabels_le_signs_mul_sparse_of_sanyal (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D) :
    (convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))).card ≤
      (minorSignPatterns D (2 ^ (8 * (D + 1) ^ (D - 1)))).card *
        (sparseSubsets (Grid D (2 ^ (8 * (D + 1) ^ (D - 1))))).card := by
  apply card_convexLabels_le_signs_mul_generators
  intro S hSlabel
  obtain ⟨z, V, _, hcard, hlabels⟩ := exists_sparse_hull_encoding_of_sanyal D hD hS S hSlabel
  exact ⟨z, V, by simpa using hcard, hlabels⟩

end VCDimConvexBound
