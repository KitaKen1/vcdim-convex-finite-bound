import VCDimConvexBound.HexagonMap

/-!
# Six closed linear sectors of the hexagon

Each sector is the image of the nonnegative quadrant under an invertible
linear map. The six sectors cover the whole plane, including their boundaries.
On each sector, the signed hexagon coefficients are a fixed linear function.
-/

namespace VCDimConvexBound

/-- Coordinates in consecutive pairs of hexagon rays, in counterclockwise order. -/
def hexSectorMap (s : Fin 6) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := ![p, (-p.2, p.1 + p.2), (-p.1 - p.2, p.1),
    (-p.1, -p.2), (p.2, -p.1 - p.2), (p.1 + p.2, -p.1)] s
  map_add' p q := by fin_cases s <;> ext <;> simp <;> ring
  map_smul' a p := by fin_cases s <;> ext <;> simp <;> ring

/-- Every sector parameterization is injective, even outside the nonnegative quadrant. -/
theorem hexSectorMap_injective (s : Fin 6) : Function.Injective (hexSectorMap s) := by
  intro p q h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  fin_cases s <;> simp [hexSectorMap] at h₁ h₂ <;> apply Prod.ext <;> linarith

/-- The six closed sectors cover the plane; overlapping boundary choices are allowed. -/
theorem exists_hexSector (p : ℝ × ℝ) :
    ∃ s : Fin 6, ∃ t : ℝ × ℝ, 0 ≤ t.1 ∧ 0 ≤ t.2 ∧ hexSectorMap s t = p := by
  rcases le_total 0 p.1 with hx | hx <;> rcases le_total 0 p.2 with hy | hy
  · exact ⟨0, p, hx, hy, rfl⟩
  · by_cases hs : 0 ≤ p.1 + p.2
    · refine ⟨5, (-p.2, p.1 + p.2), by linarith, hs, ?_⟩
      ext <;> simp [hexSectorMap]
    · refine ⟨4, (-p.1 - p.2, p.1), by linarith, hx, ?_⟩
      ext <;> simp [hexSectorMap]
  · by_cases hs : 0 ≤ p.1 + p.2
    · refine ⟨1, (p.1 + p.2, -p.1), hs, by linarith, ?_⟩
      ext <;> simp [hexSectorMap]
    · refine ⟨2, (p.2, -p.1 - p.2), hy, by linarith, ?_⟩
      ext <;> simp [hexSectorMap]
      ring
  · refine ⟨3, (-p.1, -p.2), by linarith, by linarith, ?_⟩
    ext <;> simp [hexSectorMap]

/-- On each sector, the three signed label coefficients are linear in its two parameters. -/
def hexSectorWeight (s : Fin 6) : (ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun p := ![![p.1, -p.2, 0], ![0, -p.1, p.2], ![-p.2, 0, p.1],
    ![-p.1, p.2, 0], ![0, p.1, -p.2], ![p.2, 0, -p.1]] s
  map_add' p q := by
    fin_cases s <;> funext j <;> fin_cases j <;> simp <;> ring
  map_smul' a p := by
    fin_cases s <;> funext j <;> fin_cases j <;> simp

/-- This is an equality with the actual min/max coefficients, not a new model. -/
theorem hexWeight_sub_eq_sector (s : Fin 6) (t : ℝ × ℝ)
    (ha : 0 ≤ t.1) (hb : 0 ≤ t.2) (j : Fin 3) :
    hexWeight (hexSectorMap s t) j - hexWeight (-hexSectorMap s t) j =
      hexSectorWeight s t j := by
  fin_cases s <;> fin_cases j <;>
    simp [hexWeight, hexSectorMap, hexSectorWeight] <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- Nonnegative coordinates in the product of sector parameter spaces. -/
def HexNonnegative {r : ℕ} (t : HexagonDomain r) : Prop :=
  ∀ k, 0 ≤ (t k).1 ∧ 0 ≤ (t k).2

/-- Choose one of six sectors independently for each color. -/
def hexSectorArray {r : ℕ} (s : Fin r → Fin 6) : HexagonDomain r →ₗ[ℝ] HexagonDomain r where
  toFun t k := hexSectorMap (s k) (t k)
  map_add' t u := by funext k; exact map_add _ _ _
  map_smul' a t := by
    funext k
    exact (hexSectorMap (s k)).map_smul a (t k)

theorem hexSectorArray_injective {r : ℕ} (s : Fin r → Fin 6) :
    Function.Injective (hexSectorArray s) := by
  intro t u h
  funext k
  exact hexSectorMap_injective (s k) (congrFun h k)

/-- Product sectors cover every input, not merely points in general position. -/
theorem exists_hexSectorArray {r : ℕ} (x : HexagonDomain r) :
    ∃ s : Fin r → Fin 6, ∃ t, HexNonnegative t ∧ hexSectorArray s t = x := by
  choose s t ht₁ ht₂ he using fun k => exists_hexSector (x k)
  exact ⟨s, t, fun k => ⟨ht₁ k, ht₂ k⟩, funext he⟩

theorem card_hexSectorArrays (r : ℕ) : Fintype.card (Fin r → Fin 6) = 6 ^ r := by
  simp

end VCDimConvexBound
