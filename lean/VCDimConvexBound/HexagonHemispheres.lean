import VCDimConvexBound.HexagonJoinChains
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Hemispheres of the iterated hexagon join

The full cycle in r + 1 colors is the join of the six-edge cycle with the
full cycle in r colors. A three-edge half has boundary equal to the two
antipodal cones. Each cone has boundary equal to the shifted old cycle.
These are chain identities; they do not yet prove an odd-map obstruction.
-/

namespace VCDimConvexBound

open scoped BigOperators

noncomputable def hexFundamentalChain (r : ℕ) : HexModTwoChain r :=
  ∑ s : Fin r → Fin 6, hexFaceBasis (hexFacet s)

theorem hexFundamentalChain_boundary (r : ℕ) :
    hexChainBoundary r (hexFundamentalChain r) = 0 :=
  hex_fundamental_boundary_eq_zero r

theorem hexFundamentalChain_ne_zero (r : ℕ) : hexFundamentalChain r ≠ 0 :=
  hex_fundamental_chain_ne_zero r

theorem hexModTwoChain_add_self {r : ℕ} (c : HexModTwoChain r) : c + c = 0 := by
  funext f
  exact CharTwo.add_self_eq_zero (c f)

/-- Adding the first color is exactly the join of the new edge and the old facet. -/
theorem hexFacet_cons {r : ℕ} (j : Fin 6) (s : Fin r → Fin 6) :
    hexFacet (Fin.cons j s) = hexJoinFace {j, hexNext j} (hexFacet s) := by
  ext v
  rcases v with ⟨k, l⟩
  refine Fin.cases ?_ (fun k => ?_) k
  · change (0, l) ∈ hexFacet (Fin.cons j s) ↔ hexHeadVertex l ∈ _
    rw [hexJoinFace_head_mem]
    simp [mem_hexFacet]
  · change (k.succ, l) ∈ hexFacet (Fin.cons j s) ↔ hexTailVertex (k, l) ∈ _
    rw [hexJoinFace_tail_mem]
    simp [mem_hexFacet]

/-- The six-edge recursion for the full cycle, with no geometric assumption. -/
theorem hexFundamentalChain_succ (r : ℕ) :
    hexFundamentalChain (r + 1) =
      ∑ j : Fin 6, hexPrependChain {j, hexNext j} (hexFundamentalChain r) := by
  unfold hexFundamentalChain
  simp_rw [map_sum, hexPrependChain_basis, ← hexFacet_cons]
  have h := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => Fin 6))
    (fun s => hexFaceBasis (hexFacet s))
  change (∑ x : Fin 6 × (Fin r → Fin 6),
    hexFaceBasis (hexFacet (Fin.cons x.1 x.2))) = _ at h
  simpa only [Fintype.sum_prod_type] using h.symm

/-- A cone over the old fundamental cycle at a vertex of the new hexagon. -/
noncomputable def hexConeChain (r : ℕ) (j : Fin 6) : HexModTwoChain (r + 1) :=
  hexPrependChain {j} (hexFundamentalChain r)

/-- The half using consecutive edges 0--1, 1--2, and 2--3. -/
noncomputable def hexHemisphereChain (r : ℕ) : HexModTwoChain (r + 1) :=
  ∑ j ∈ ({0, 1, 2} : Finset (Fin 6)),
    hexPrependChain {j, hexNext j} (hexFundamentalChain r)

/-- Boundary of a cone is the old cycle embedded in the remaining colors. -/
theorem hexConeChain_boundary (r : ℕ) (j : Fin 6) :
    hexChainBoundary (r + 1) (hexConeChain r j) =
      hexPrependChain ∅ (hexFundamentalChain r) := by
  simp [hexConeChain, hexChainBoundary_prepend, hexFundamentalChain_boundary]

/-- Boundary of the join of a new edge with the old cycle. -/
theorem hexEdgeChain_boundary (r : ℕ) (j : Fin 6) :
    hexChainBoundary (r + 1)
      (hexPrependChain {j, hexNext j} (hexFundamentalChain r)) =
        hexConeChain r j + hexConeChain r (hexNext j) := by
  have hj := hexNext_ne_self j
  have he : ({j, hexNext j} : Finset (Fin 6)).erase (hexNext j) = {j} := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hk₁ | hk₂⟩
      · exact hk₁
      · exact (hk hk₂).elim
    · intro hk
      subst k
      exact ⟨Ne.symm hj, Or.inl rfl⟩
  simp [hexChainBoundary_prepend, hexFundamentalChain_boundary,
    hexConeChain, he, Ne.symm hj, add_comm]

/-- Internal cones cancel: the half has just two antipodal cones as boundary. -/
theorem hexHemisphereChain_boundary (r : ℕ) :
    hexChainBoundary (r + 1) (hexHemisphereChain r) =
      hexConeChain r 0 + hexConeChain r 3 := by
  unfold hexHemisphereChain
  simp_rw [map_sum, hexEdgeChain_boundary]
  have h : (∑ j ∈ ({0, 1, 2} : Finset (Fin 6)),
      (hexConeChain r j + hexConeChain r (hexNext j))) =
      (hexConeChain r 0 + hexConeChain r 1) +
      (hexConeChain r 1 + hexConeChain r 2) +
      (hexConeChain r 2 + hexConeChain r 3) := by
    simp [hexNext, add_assoc]
  rw [h]
  calc
    _ = (hexConeChain r 0 + hexConeChain r 3) +
        (hexConeChain r 1 + hexConeChain r 1) +
        (hexConeChain r 2 + hexConeChain r 2) := by abel
    _ = _ := by simp [hexModTwoChain_add_self]

end VCDimConvexBound
