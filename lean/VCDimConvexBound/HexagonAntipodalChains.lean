import VCDimConvexBound.HexagonHemispheres

/-!
# Antipodal symmetry of the hemisphere chains

The antipodal operator changes every color simultaneously. It commutes with
the actual boundary and fixes the full cycle. The full cycle is the sum of a
half and its antipode; the boundary of the half is a cone plus its antipode.
-/

namespace VCDimConvexBound

open scoped BigOperators

theorem hexVertexOpposite_involutive (r : ℕ) :
    Function.Involutive (@hexVertexOpposite r) := by
  intro v
  exact Prod.ext rfl (hexOpposite_involutive v.2)

theorem hexFacet_image_opposite {r : ℕ} (s : Fin r → Fin 6) :
    (hexFacet s).image hexVertexOpposite = hexFacet (hexOpposite ∘ s) := by
  apply Finset.Subset.antisymm
  · rintro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (hexVertexOpposite_mem_facet_iff s w).mpr hw
  · intro v hv
    refine Finset.mem_image.mpr ⟨hexVertexOpposite v, ?_, hexVertexOpposite_involutive r v⟩
    apply (hexVertexOpposite_mem_facet_iff s (hexVertexOpposite v)).mp
    rw [hexVertexOpposite_involutive r v]
    exact hv

theorem hexJoinFace_image_opposite {r : ℕ} (a : Finset (Fin 6))
    (t : Finset (HexVertex r)) :
    (hexJoinFace a t).image hexVertexOpposite =
      hexJoinFace (a.image hexOpposite) (t.image hexVertexOpposite) := by
  simp only [hexJoinFace, Finset.image_union, Finset.image_image]
  rfl

/-- Push a chain through the antipodal involution on all its vertices. -/
noncomputable def hexAntipodalChain (r : ℕ) : HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain r where
  toFun c := ∑ t : Finset (HexVertex r), c t • hexFaceBasis (t.image hexVertexOpposite)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' x c := by simp [smul_smul, Finset.smul_sum]

theorem hexAntipodalChain_basis {r : ℕ} (t : Finset (HexVertex r)) :
    hexAntipodalChain r (hexFaceBasis t) = hexFaceBasis (t.image hexVertexOpposite) := by
  simp [hexAntipodalChain, hexFaceBasis]

theorem hexAntipodalChain_involutive (r : ℕ) :
    Function.Involutive (hexAntipodalChain r) := by
  intro c
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexAntipodalChain_basis, Finset.image_image]
  rw [show (hexVertexOpposite ∘ hexVertexOpposite : HexVertex r → HexVertex r) = id
    from funext (hexVertexOpposite_involutive r)]
  simp only [Finset.image_id]

/-- The global antipodal map is a chain map for the deletion boundary. -/
theorem hexAntipodalChain_boundary {r : ℕ} (c : HexModTwoChain r) :
    hexAntipodalChain r (hexChainBoundary r c) =
      hexChainBoundary r (hexAntipodalChain r c) := by
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexChainBoundary_basis, hexAntipodalChain_basis]
  congr 1
  funext t
  congr 1
  rw [Finset.sum_image]
  · simp_rw [Finset.image_erase (hexVertexOpposite_involutive r).injective]
  · exact fun a _ b _ h => (hexVertexOpposite_involutive r).injective h

/-- The action on a join is antipodal in both the new and old colors. -/
theorem hexAntipodalChain_prepend {r : ℕ} (a : Finset (Fin 6)) (c : HexModTwoChain r) :
    hexAntipodalChain (r + 1) (hexPrependChain a c) =
      hexPrependChain (a.image hexOpposite) (hexAntipodalChain r c) := by
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexPrependChain_basis, hexAntipodalChain_basis,
    hexJoinFace_image_opposite]

/-- All facets together are invariant under the global antipode. -/
theorem hexFundamentalChain_antipodal (r : ℕ) :
    hexAntipodalChain r (hexFundamentalChain r) = hexFundamentalChain r := by
  unfold hexFundamentalChain
  simp_rw [map_sum, hexAntipodalChain_basis, hexFacet_image_opposite]
  let e : (Fin r → Fin 6) ≃ (Fin r → Fin 6) :=
    { toFun := fun s => hexOpposite ∘ s
      invFun := fun s => hexOpposite ∘ s
      left_inv := fun s => funext (fun k => hexOpposite_involutive (s k))
      right_inv := fun s => funext (fun k => hexOpposite_involutive (s k)) }
  exact Equiv.sum_comp e (fun s => hexFaceBasis (hexFacet s))

theorem hexConeChain_antipodal (r : ℕ) (j : Fin 6) :
    hexAntipodalChain (r + 1) (hexConeChain r j) = hexConeChain r (hexOpposite j) := by
  simp [hexConeChain, hexAntipodalChain_prepend, hexFundamentalChain_antipodal]

/-- The half-boundary formula expressed using the genuine global antipode. -/
theorem hexHemisphereChain_boundary_antipodal (r : ℕ) :
    hexChainBoundary (r + 1) (hexHemisphereChain r) =
      hexConeChain r 0 + hexAntipodalChain (r + 1) (hexConeChain r 0) := by
  rw [hexConeChain_antipodal, hexHemisphereChain_boundary]
  rfl

/-- The two antipodal halves sum to the full cycle in every number of colors. -/
theorem hexFundamentalChain_eq_hemisphere_add_antipodal (r : ℕ) :
    hexFundamentalChain (r + 1) = hexHemisphereChain r +
      hexAntipodalChain (r + 1) (hexHemisphereChain r) := by
  rw [hexFundamentalChain_succ]
  unfold hexHemisphereChain
  simp_rw [map_sum, hexAntipodalChain_prepend, hexFundamentalChain_antipodal,
    Finset.image_insert, Finset.image_singleton, hexOpposite_next]
  simp [Fin.sum_univ_succ, hexNext, hexOpposite]
  abel

end VCDimConvexBound
