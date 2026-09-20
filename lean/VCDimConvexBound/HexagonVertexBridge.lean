import VCDimConvexBound.HexagonRealization

/-!
# Barycentric facet zeros give the actual normalized cone certificate

The two coordinate unit vectors in each color map to the actual vertices
of the selected hexagon facet. The concrete map is linear on that sector,
so its value is the corresponding weighted sum of vertex images.
-/

namespace VCDimConvexBound

open scoped BigOperators

theorem hexDomainVertex_opposite {r : ℕ} (v : HexVertex r) :
    hexDomainVertex (hexVertexOpposite v) = -hexDomainVertex v := by
  funext k
  simp only [hexDomainVertex, hexVertexOpposite, Pi.neg_apply]
  by_cases h : k = v.1
  · simp [h, hexSectorMap_opposite]
  · simp [h]

/-- The two endpoints per color enumerate the actual facet without repetition. -/
noncomputable def hexFacetVertexEquiv {r : ℕ} (s : Fin r → Fin 6) :
    (Fin r × Bool) ≃ hexFacet s :=
  Equiv.ofBijective (fun e => ⟨hexFacetVertex s e, hexFacetVertex_mem s e⟩) (by
    constructor
    · intro i j h
      exact hexFacetVertex_injective s (congrArg Subtype.val h)
    · rintro ⟨v, hv⟩
      obtain ⟨e, _, he⟩ := Finset.mem_image.mp hv
      exact ⟨e, Subtype.ext he⟩)

/-- A unit vector in one of the two nonnegative coordinates of one color. -/
def hexParameterVertex {r : ℕ} (e : Fin r × Bool) : HexagonDomain r :=
  fun k => if k = e.1 then (if e.2 then (0, 1) else (1, 0)) else 0

theorem hexParameterVertex_nonnegative {r : ℕ} (e : Fin r × Bool) :
    HexNonnegative (hexParameterVertex e) := by
  intro k
  rcases e with ⟨l, b⟩
  cases b <;> by_cases h : k = l <;> simp [hexParameterVertex, h]

theorem hexSectorArray_parameterVertex {r : ℕ} (s : Fin r → Fin 6)
    (e : Fin r × Bool) :
    hexSectorArray s (hexParameterVertex e) = hexDomainVertex (hexFacetVertex s e) := by
  rcases e with ⟨l, b⟩
  funext k
  by_cases h : k = l
  · subst k
    cases b
    · simp [hexSectorArray, hexParameterVertex, hexDomainVertex, hexFacetVertex]
    · have he := hexSectorMap_eq_ray_combination (s l) (0, 1)
      simpa [hexSectorArray, hexParameterVertex, hexDomainVertex, hexFacetVertex] using he
  · simp [hexSectorArray, hexParameterVertex, hexDomainVertex, hexFacetVertex, h]

/-- The actual vertex images are evaluations of the same linear piece. -/
theorem hexPieceLinear_parameterVertex {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (e : Fin r × Bool) :
    hexPieceLinear z s (hexParameterVertex e) =
      hexagonCayleyMap z (hexDomainVertex (hexFacetVertex s e)) := by
  rw [← hexagonCayleyMap_sector z s _ (hexParameterVertex_nonnegative e),
    hexSectorArray_parameterVertex]

/-- The parameter vector associated to arbitrary endpoint weights. -/
def hexParametersOfWeights {r : ℕ} (w : Fin r × Bool → ℝ) : HexagonDomain r :=
  fun k => (w (k, false), w (k, true))

theorem hexParametersOfWeights_eq_sum {r : ℕ} (w : Fin r × Bool → ℝ) :
    hexParametersOfWeights w = ∑ e, w e • hexParameterVertex e := by
  funext k
  apply Prod.ext <;>
    simp [hexParametersOfWeights, hexParameterVertex, Finset.sum_apply,
      Fintype.sum_prod_type]

theorem hexParameterMass_ofWeights {r : ℕ} (w : Fin r × Bool → ℝ) :
    hexParameterMass (hexParametersOfWeights w) = ∑ e, w e := by
  simp [hexParameterMass, hexParametersOfWeights, Fintype.sum_prod_type, add_comm]

/-- On a selected facet, the concrete nonlinear formula has the expected
linear interpolation of its actual vertex images. -/
theorem hexPieceLinear_ofWeights {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (w : Fin r × Bool → ℝ) :
    hexPieceLinear z s (hexParametersOfWeights w) =
      ∑ e, w e • hexagonCayleyMap z (hexDomainVertex (hexFacetVertex s e)) := by
  rw [hexParametersOfWeights_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_smul, hexPieceLinear_parameterVertex]

/-- A barycentric zero of the actual facet vertex images is the required
nonnegative mass-one kernel vector of its concrete linear piece. -/
theorem exists_hexPiece_kernel_of_facet_zero {r D : ℕ}
    (z : Fin r → Fin 3 → Point D) (s : Fin r → Fin 6)
    (x : (hexFacet s) → ℝ) (hm : ∑ v, x v = 1) (hx : ∀ v, 0 ≤ x v)
    (hz : ∑ v, x v • hexagonCayleyMap z (hexDomainVertex v.val) = 0) :
    ∃ t : HexagonDomain r,
      HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0 := by
  let w : Fin r × Bool → ℝ := fun e => x (hexFacetVertexEquiv s e)
  refine ⟨hexParametersOfWeights w, ?_, ?_, ?_⟩
  · intro k
    exact ⟨hx _, hx _⟩
  · rw [hexParameterMass_ofWeights]
    exact ((hexFacetVertexEquiv s).sum_comp x).trans hm
  · rw [hexPieceLinear_ofWeights]
    exact ((hexFacetVertexEquiv s).sum_comp
      (fun v => x v • hexagonCayleyMap z (hexDomainVertex v.val))).trans hz

end VCDimConvexBound
