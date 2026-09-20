import VCDimConvexBound.HexagonSymmetry

/-!
# Compatibility of normalized sector certificates on overlaps

The hexagonal radius recovers the sum of nonnegative sector coordinates,
independently of the sector chosen. Thus both the linear map and the mass-one
normalization agree on overlaps. Updating a boundary coordinate gives an
explicit move to an adjacent product sector that preserves certificates.
-/

namespace VCDimConvexBound

/-- A coordinate-independent radius for the unit hexagon. -/
noncomputable def hexRadius (p : ℝ × ℝ) : ℝ :=
  max |p.1| (max |p.2| |p.1 + p.2|)

/-- On any nonnegative sector, radius is exactly coordinate mass. -/
theorem hexRadius_sector (s : Fin 6) (t : ℝ × ℝ)
    (ht : 0 ≤ t.1 ∧ 0 ≤ t.2) : hexRadius (hexSectorMap s t) = t.1 + t.2 := by
  fin_cases s <;> simp [hexRadius, hexSectorMap] <;>
    simp only [abs_eq_max_neg, max_def] <;> split_ifs <;> linarith [ht.1, ht.2]

/-- The sector-coordinate mass does not depend on the presentation of a point. -/
theorem hexSectorMass_eq_of_eq (s s' : Fin 6) (t u : ℝ × ℝ)
    (ht : 0 ≤ t.1 ∧ 0 ≤ t.2) (hu : 0 ≤ u.1 ∧ 0 ≤ u.2)
    (he : hexSectorMap s t = hexSectorMap s' u) : t.1 + t.2 = u.1 + u.2 := by
  rw [← hexRadius_sector s t ht, ← hexRadius_sector s' u hu, he]

/-- All product-sector overlaps, including higher-codimension ones, preserve mass. -/
theorem hexParameterMass_eq_of_sectorArray_eq {r : ℕ}
    (s s' : Fin r → Fin 6) (t u : HexagonDomain r)
    (ht : HexNonnegative t) (hu : HexNonnegative u)
    (he : hexSectorArray s t = hexSectorArray s' u) :
    hexParameterMass t = hexParameterMass u := by
  change (∑ k, ((t k).1 + (t k).2)) = ∑ k, ((u k).1 + (u k).2)
  apply Finset.sum_congr rfl
  intro k _
  exact hexSectorMass_eq_of_eq (s k) (s' k) (t k) (u k) (ht k) (hu k) (congrFun he k)

/-- Linear pieces agree wherever their nonnegative sector images overlap. -/
theorem hexPieceLinear_eq_of_sectorArray_eq {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s s' : Fin r → Fin 6) (t u : HexagonDomain r)
    (ht : HexNonnegative t) (hu : HexNonnegative u)
    (he : hexSectorArray s t = hexSectorArray s' u) :
    hexPieceLinear z s t = hexPieceLinear z s' u := by
  rw [← hexagonCayleyMap_sector z s t ht, ← hexagonCayleyMap_sector z s' u hu, he]

/-- Normalized zero certificates are independent of the chosen sector coordinates. -/
theorem hex_normalized_kernel_overlap_iff {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s s' : Fin r → Fin 6) (t u : HexagonDomain r)
    (ht : HexNonnegative t) (hu : HexNonnegative u)
    (he : hexSectorArray s t = hexSectorArray s' u) :
    (hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0) ↔
      (hexParameterMass u = 1 ∧ hexPieceLinear z s' u = 0) := by
  rw [hexParameterMass_eq_of_sectorArray_eq s s' t u ht hu he,
    hexPieceLinear_eq_of_sectorArray_eq z s s' t u ht hu he]

/-- Move one boundary coordinate to the next sector without changing its point. -/
theorem hexSectorArray_boundary_update {r : ℕ} (s : Fin r → Fin 6)
    (t : HexagonDomain r) (k : Fin r) (hk : (t k).1 = 0) :
    hexSectorArray (Function.update s k (hexNext (s k)))
      (Function.update t k ((t k).2, 0)) = hexSectorArray s t := by
  funext j
  by_cases hj : j = k
  · subst j
    simp only [hexSectorArray, LinearMap.coe_mk, AddHom.coe_mk, Function.update_self]
    have ht : t k = (0, (t k).2) := Prod.ext hk rfl
    conv_rhs => rw [ht]
    exact (hexSectorMap_boundary (s k) (t k).2).symm
  · simp [hexSectorArray, Function.update_of_ne hj]

/-- The explicit boundary move keeps all coordinates nonnegative. -/
theorem HexNonnegative.boundary_update {r : ℕ} {t : HexagonDomain r}
    (ht : HexNonnegative t) (k : Fin r) :
    HexNonnegative (Function.update t k ((t k).2, 0)) := by
  intro j
  by_cases hj : j = k
  · subst j
    simpa using And.intro (ht k).2 (le_refl (0 : ℝ))
  · simpa [Function.update_of_ne hj] using ht j

/-- A normalized kernel certificate passes across any available boundary face. -/
theorem hex_normalized_kernel_boundary_update {r D : ℕ}
    (z : Fin r → Fin 3 → Point D) (s : Fin r → Fin 6) (t : HexagonDomain r)
    (ht : HexNonnegative t) (hm : hexParameterMass t = 1)
    (hz : hexPieceLinear z s t = 0) (k : Fin r) (hk : (t k).1 = 0) :
    HexNonnegative (Function.update t k ((t k).2, 0)) ∧
      hexParameterMass (Function.update t k ((t k).2, 0)) = 1 ∧
      hexPieceLinear z (Function.update s k (hexNext (s k)))
        (Function.update t k ((t k).2, 0)) = 0 := by
  have hu := ht.boundary_update k
  refine ⟨hu, ?_⟩
  exact (hex_normalized_kernel_overlap_iff z _ _ _ _ hu ht
    (hexSectorArray_boundary_update s t k hk)).mpr ⟨hm, hz⟩

end VCDimConvexBound
