import VCDimConvexBound.HexagonCochainParity
import VCDimConvexBound.FlagCrossingSymmetry
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Enumerating actual hexagon faces and their deleted faces

Crossing indicators will use the subtype of vertices in a face. These
equivalences connect that subtype to the finite column indices of the
local matrix theorems, including deletion and the genuine antipodal map.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Any prescribed cardinality supplies an enumeration of a face. -/
noncomputable def hexFaceEnumeration {r n : ℕ} (f : Finset (HexVertex r))
    (hf : f.card = n) : Fin n ≃ f := (f.equivFinOfCardEq hf).symm

/-- Delete one index from an enumeration and one vertex from the actual face. -/
noncomputable def hexFaceEraseEnumeration {r n : ℕ} {f : Finset (HexVertex r)}
    (e : Fin (n + 1) ≃ f) (i : Fin (n + 1)) : Fin n ≃ (f.erase (e i).val) :=
  Equiv.ofBijective
    (fun j => ⟨(e (i.succAbove j)).val, Finset.mem_erase.mpr
      ⟨fun h => i.succAbove_ne j (e.injective (Subtype.ext h)), (e _).property⟩⟩) (by
    constructor
    · intro j l h
      have hv : (e (i.succAbove j)).val = (e (i.succAbove l)).val :=
        congrArg (fun v : (f.erase (e i).val) => v.val) h
      exact Fin.succAbove_right_injective (e.injective (Subtype.ext hv))
    · intro v
      obtain ⟨hvne, hvf⟩ := Finset.mem_erase.mp v.property
      obtain ⟨j, hj⟩ := e.surjective ⟨v.val, hvf⟩
      rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨l, rfl⟩
      · subst j
        exact (hvne (congrArg Subtype.val hj).symm).elim
      · refine ⟨l, Subtype.ext ?_⟩
        exact congrArg (fun w : f => w.val) hj)

theorem hexFaceEraseEnumeration_val {r n : ℕ} {f : Finset (HexVertex r)}
    (e : Fin (n + 1) ≃ f) (i : Fin (n + 1)) (j : Fin n) :
    (hexFaceEraseEnumeration e i j).val = (e (i.succAbove j)).val := rfl

/-- The genuine antipode gives a bijection of face vertex subtypes. -/
noncomputable def hexFaceAntipodalEquiv {r : ℕ} (f : Finset (HexVertex r)) :
    f ≃ (f.image hexVertexOpposite) :=
  Equiv.ofBijective
    (fun v => ⟨hexVertexOpposite v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩) (by
    constructor
    · intro v w h
      exact Subtype.ext ((hexVertexOpposite_involutive r).injective (congrArg Subtype.val h))
    · intro v
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp v.property
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩)

theorem hexFaceAntipodalEquiv_val {r : ℕ} (f : Finset (HexVertex r)) (v : f) :
    (hexFaceAntipodalEquiv f v).val = hexVertexOpposite v.val := rfl

/-- Summing over enumerated deletions is the actual simplicial coboundary. -/
theorem hexCoboundary_eq_sum_enumeration {r n : ℕ} (a : HexModTwoChain r)
    (f : Finset (HexVertex r)) (e : Fin n ≃ f) :
    hexCoboundary a f = ∑ i : Fin n, a (f.erase (e i).val) := by
  have h := e.sum_comp (fun v : f => a (f.erase v.val))
  change (∑ v ∈ f, a (f.erase v)) = _
  rw [← Finset.sum_attach f (fun v => a (f.erase v))]
  exact h.symm

end VCDimConvexBound
