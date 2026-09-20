import VCDimConvexBound.HullEncoding
import VCDimConvexBound.DensityConstants

/-!
# The precise remaining geometric input and its sparse-generator consequence

`SanyalBoxObstruction` is a proposition, not an axiom or a proved theorem.
It is the special consequence of Sanyal's Theorem 1.3 required by the VC argument:
the complete sums of D families of D+1 points in R^D cannot be convex independent.
The reference allows lower-dimensional summands (Observation 1).

This file proves the reduction from that explicit input to sparse representatives.
It does not prove the geometric input itself.

Reference: https://arxiv.org/pdf/math/0702717v2
-/

namespace VCDimConvexBound

/-- The geometric input still to be proved, intended for `2 ≤ D`. -/
def SanyalBoxObstruction (D : ℕ) : Prop :=
  ∀ z : Fin D → Fin (D + 1) → Point D,
    ¬ ConvexIndependent ℝ (gridSum z)

/-- A convex-independent family cannot contain a full box if the geometric input holds. -/
theorem not_containsBox_of_sanyal {D m : ℕ}
    (hS : SanyalBoxObstruction D) (z : Fin D → Fin m → Point D)
    (V : Finset (Grid D m)) (hV : ConvexIndependentOn (gridSum z) V) :
    ¬ ContainsBox V (D + 1) := by
  classical
  rintro ⟨A, hA, hAV⟩
  let e (k : Fin D) : Fin (D + 1) ≃ A k :=
    (Fintype.equivFinOfCardEq (by simpa using hA k)).symm
  let emb : Grid D (D + 1) ↪ V :=
    { toFun := fun i => ⟨fun k => (e k (i k)).val,
        hAV _ (fun k => (e k (i k)).property)⟩
      inj' := by
        intro i j h
        funext k
        apply (e k).injective
        apply Subtype.ext
        exact congrFun (congrArg Subtype.val h) k }
  let w : Fin D → Fin (D + 1) → Point D := fun k a => z k (e k a)
  apply hS w
  exact hV.convexIndependent.comp_embedding emb

/-- P3 and the geometric input bound the number of convex-independent representatives. -/
theorem convexIndependent_card_lt_of_sanyal (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D)
    (z : Fin D → Fin (2 ^ (8 * (D + 1) ^ (D - 1))) → Point D)
    (V : Finset (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))))
    (hV : ConvexIndependentOn (gridSum z) V) :
    16 * V.card < (2 ^ (8 * (D + 1) ^ (D - 1))) ^ D := by
  by_contra h
  have hbox := containsBox_of_density_one_sixteenth D hD V (by omega)
  exact not_containsBox_of_sanyal hS z V hV hbox

/-- Every convex label has a sparse hull encoding, conditional on the geometric input. -/
theorem exists_sparse_hull_encoding_of_sanyal (D : ℕ) (hD : 2 ≤ D)
    (hS : SanyalBoxObstruction D)
    (S : Set (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))) )
    (hSlabel : S ∈ convexLabels D (2 ^ (8 * (D + 1) ^ (D - 1)))) :
    ∃ z : Fin D → Fin (2 ^ (8 * (D + 1) ^ (D - 1))) → Point D,
      ∃ V : Finset (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))),
        ConvexIndependentOn (gridSum z) V ∧
        16 * V.card < (2 ^ (8 * (D + 1) ^ (D - 1))) ^ D ∧
        ∀ i, i ∈ S ↔ gridSum z i ∈ indexedHull (gridSum z) V := by
  obtain ⟨C, hC, z, hz⟩ := mem_convexLabels.mp hSlabel
  obtain ⟨V, _, hV, _, hlabels⟩ := exists_label_generators (gridSum z) C hC
  exact ⟨z, V, hV, convexIndependent_card_lt_of_sanyal D hD hS z V hV,
    fun i => (hz i).symm.trans (hlabels i)⟩

end VCDimConvexBound
