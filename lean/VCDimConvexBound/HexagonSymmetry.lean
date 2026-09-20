import VCDimConvexBound.HexagonLinearPieces

/-!
# Adjacent sectors and the antipodal symmetry

The six-sector presentation comes with explicit boundary identifications and
an involution without fixed sectors. The opposite linear pieces are negatives
on the same coordinates; normalized kernel certificates occur in pairs.
-/

namespace VCDimConvexBound

/-- The next sector in cyclic order. -/
def hexNext (s : Fin 6) : Fin 6 := s + 1

/-- The antipodal sector, three steps further around the hexagon. -/
def hexOpposite (s : Fin 6) : Fin 6 := s + 3

theorem hexOpposite_involutive : Function.Involutive hexOpposite := by
  intro s
  fin_cases s <;> decide

theorem hexOpposite_ne_self (s : Fin 6) : hexOpposite s ≠ s := by
  fin_cases s <;> decide

theorem hexOpposite_next (s : Fin 6) : hexOpposite (hexNext s) = hexNext (hexOpposite s) := by
  fin_cases s <;> decide

/-- The outgoing ray of a sector is the incoming ray of the next one. -/
theorem hexSectorMap_boundary (s : Fin 6) (a : ℝ) :
    hexSectorMap s (0, a) = hexSectorMap (hexNext s) (a, 0) := by
  fin_cases s <;> ext <;> simp [hexNext, hexSectorMap]

/-- Adjacent closed sectors meet exactly in their common ray. -/
theorem hexSectorMap_adjacent_eq_iff (s : Fin 6) (u v : ℝ × ℝ)
    (hu : 0 ≤ u.1 ∧ 0 ≤ u.2) (hv : 0 ≤ v.1 ∧ 0 ≤ v.2) :
    hexSectorMap s u = hexSectorMap (hexNext s) v ↔
      u.1 = 0 ∧ v.2 = 0 ∧ u.2 = v.1 := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    fin_cases s <;> simp [hexNext, hexSectorMap] at h₁ h₂ <;>
      refine ⟨?_, ?_, ?_⟩ <;> linarith [hu.1, hu.2, hv.1, hv.2]
  · rintro ⟨ha, hb, hc⟩
    have hu' : u = (0, u.2) := Prod.ext ha rfl
    have hv' : v = (u.2, 0) := Prod.ext hc.symm hb
    rw [hu', hv', hexSectorMap_boundary]

/-- Opposite sectors represent opposite points with unchanged parameters. -/
theorem hexSectorMap_opposite (s : Fin 6) (t : ℝ × ℝ) :
    hexSectorMap (hexOpposite s) t = -hexSectorMap s t := by
  fin_cases s <;> ext <;> simp [hexOpposite, hexSectorMap] <;> ring

/-- The linear coefficient vectors on opposite sectors negate one another. -/
theorem hexSectorWeight_opposite (s : Fin 6) (t : ℝ × ℝ) :
    hexSectorWeight (hexOpposite s) t = -hexSectorWeight s t := by
  fin_cases s <;> funext j <;> fin_cases j <;> simp [hexOpposite, hexSectorWeight]

/-- The product-sector involution realizes the antipodal action on the domain. -/
theorem hexSectorArray_opposite {r : ℕ} (s : Fin r → Fin 6) (t : HexagonDomain r) :
    hexSectorArray (hexOpposite ∘ s) t = -hexSectorArray s t := by
  funext k
  exact hexSectorMap_opposite (s k) (t k)

/-- Opposite extensions have the same kernel, without a nonnegativity assumption. -/
theorem hexPieceLinear_opposite {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (t : HexagonDomain r) :
    hexPieceLinear z (hexOpposite ∘ s) t = -hexPieceLinear z s t := by
  simp [hexPieceLinear, hexSectorWeight_opposite, Finset.sum_neg_distrib]

theorem hexPieceLinear_opposite_eq_zero_iff {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (t : HexagonDomain r) :
    hexPieceLinear z (hexOpposite ∘ s) t = 0 ↔ hexPieceLinear z s t = 0 := by
  rw [hexPieceLinear_opposite, neg_eq_zero]

/-- Every certificate has an antipodal partner with exactly the same coordinates. -/
theorem hex_normalized_kernel_opposite_iff {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (t : HexagonDomain r) :
    (HexNonnegative t ∧ hexParameterMass t = 1 ∧
      hexPieceLinear z (hexOpposite ∘ s) t = 0) ↔
    (HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0) := by
  rw [hexPieceLinear_opposite_eq_zero_iff]

/-- Exactly one of a sector and its opposite lies in the first three sectors. -/
theorem hexOpposite_lt_three_iff (s : Fin 6) :
    (hexOpposite s).val < 3 ↔ 3 ≤ s.val := by
  fin_cases s <;> decide

/-- It suffices to search one representative of each antipodal pair.
The choice is global: all sectors are negated together, not independently. -/
theorem exists_hex_normalized_kernel_first_half_iff {r D : ℕ}
    (z : Fin r → Fin 3 → Point D) (k : Fin r) :
    (∃ s : Fin r → Fin 6, ∃ t : HexagonDomain r,
      HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0) ↔
    (∃ s : Fin r → Fin 6, ∃ t : HexagonDomain r,
      (s k).val < 3 ∧ HexNonnegative t ∧ hexParameterMass t = 1 ∧
        hexPieceLinear z s t = 0) := by
  constructor
  · rintro ⟨s, t, ht, hm, hz⟩
    by_cases hs : (s k).val < 3
    · exact ⟨s, t, hs, ht, hm, hz⟩
    · refine ⟨hexOpposite ∘ s, t, ?_, ht, hm, ?_⟩
      · exact (hexOpposite_lt_three_iff (s k)).mpr (by omega)
      · rw [hexPieceLinear_opposite, hz, neg_zero]
  · rintro ⟨s, t, _, ht, hm, hz⟩
    exact ⟨s, t, ht, hm, hz⟩

end VCDimConvexBound
