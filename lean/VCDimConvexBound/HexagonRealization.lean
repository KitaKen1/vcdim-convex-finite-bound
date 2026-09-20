import VCDimConvexBound.HexagonModTwo

/-!
# Realizing the hexagon-join facets in the actual input space

Nonnegative parameters of mass one are the barycentric weights of the
2r vertices of the corresponding abstract facet. Thus the finite domain
used for the boundary calculation is connected to the original hexagon map.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Place one hexagon ray in the indicated color plane. -/
def hexDomainVertex {r : ℕ} (v : HexVertex r) : HexagonDomain r :=
  fun k => if k = v.1 then hexSectorMap v.2 (1, 0) else 0

/-- The sector parameters, indexed by the two vertices in each color. -/
def hexFacetWeight {r : ℕ} (t : HexagonDomain r) (e : Fin r × Bool) : ℝ :=
  if e.2 then (t e.1).2 else (t e.1).1

theorem hexFacetWeight_nonneg {r : ℕ} (t : HexagonDomain r) (ht : HexNonnegative t)
    (e : Fin r × Bool) : 0 ≤ hexFacetWeight t e := by
  rcases e with ⟨k, b⟩
  cases b
  · exact (ht k).1
  · exact (ht k).2

theorem sum_hexFacetWeight {r : ℕ} (t : HexagonDomain r) :
    (∑ e : Fin r × Bool, hexFacetWeight t e) = hexParameterMass t := by
  simp [hexFacetWeight, Fintype.sum_prod_type, hexParameterMass, add_comm]

/-- The two ray generators recover the linear sector parameterization. -/
theorem hexSectorMap_eq_ray_combination (s : Fin 6) (t : ℝ × ℝ) :
    hexSectorMap s t = t.1 • hexSectorMap s (1, 0) +
      t.2 • hexSectorMap (hexNext s) (1, 0) := by
  fin_cases s <;> ext <;> simp [hexSectorMap, hexNext] <;> ring

/-- The actual point is the weighted sum of the vertices of the abstract facet. -/
theorem hexSectorArray_eq_facet_combination {r : ℕ} (s : Fin r → Fin 6)
    (t : HexagonDomain r) :
    hexSectorArray s t = ∑ e : Fin r × Bool,
      hexFacetWeight t e • hexDomainVertex (hexFacetVertex s e) := by
  funext k
  change hexSectorMap (s k) (t k) = _
  rw [hexSectorMap_eq_ray_combination]
  simp [hexFacetWeight, hexDomainVertex, hexFacetVertex, Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]

/-- Every normalized nonnegative sector point has actual barycentric coordinates. -/
theorem hexSectorArray_normalized_barycentric {r : ℕ} (s : Fin r → Fin 6)
    (t : HexagonDomain r) (ht : HexNonnegative t) (hm : hexParameterMass t = 1) :
    (∀ e, 0 ≤ hexFacetWeight t e) ∧ (∑ e, hexFacetWeight t e) = 1 ∧
      hexSectorArray s t = ∑ e, hexFacetWeight t e • hexDomainVertex (hexFacetVertex s e) :=
  ⟨hexFacetWeight_nonneg t ht, (sum_hexFacetWeight t).trans hm,
    hexSectorArray_eq_facet_combination s t⟩

end VCDimConvexBound
