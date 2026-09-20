import VCDimConvexBound.CayleyCentered

/-!
# Explicit hexagon coefficients

The positive labels occupy alternating rays of the hexagon. The negative
coefficients are the same functions at the antipodal point. All claims are
for arbitrary real coordinates, including sector boundaries and the origin.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The three positive labels on rays (1,0), (0,-1), (-1,1). -/
noncomputable def hexWeight (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![max 0 (min p.1 (p.1 + p.2)),
    max 0 (min (-p.2) (-p.1 - p.2)),
    max 0 (min (-p.1) p.2)]

theorem hexWeight_nonneg (p : ℝ × ℝ) (j : Fin 3) : 0 ≤ hexWeight p j := by
  fin_cases j <;> simp [hexWeight]

/-- Among the three positive labels, at most one coefficient is nonzero. -/
theorem hexWeight_colorful (p : ℝ × ℝ) (i j : Fin 3)
    (hi : hexWeight p i ≠ 0) (hj : hexWeight p j ≠ 0) : i = j := by
  have hi' := lt_of_le_of_ne (hexWeight_nonneg p i) (Ne.symm hi)
  have hj' := lt_of_le_of_ne (hexWeight_nonneg p j) (Ne.symm hj)
  fin_cases i <;> fin_cases j <;>
    simp_all [hexWeight] <;> linarith

/-- A positive and a negative coefficient never use the same label. -/
theorem hexWeight_disjoint (p : ℝ × ℝ) (j : Fin 3) :
    hexWeight p j = 0 ∨ hexWeight (-p) j = 0 := by
  by_contra h
  push Not at h
  have ha := lt_of_le_of_ne (hexWeight_nonneg p j) (Ne.symm h.1)
  have hb := lt_of_le_of_ne (hexWeight_nonneg (-p) j) (Ne.symm h.2)
  fin_cases j <;> simp_all [hexWeight] <;> linarith

/-- The six coefficients vanish simultaneously only at the origin. -/
theorem eq_zero_of_hexWeight_eq_zero (p : ℝ × ℝ)
    (ha : ∀ j, hexWeight p j = 0) (hb : ∀ j, hexWeight (-p) j = 0) : p = 0 := by
  have hmin (u v : ℝ) (h : max 0 (min u v) = 0) : u ≤ 0 ∨ v ≤ 0 := by
    apply min_le_iff.mp
    exact (le_max_right 0 (min u v)).trans_eq h
  have ha0 := hmin p.1 (p.1 + p.2) (ha 0)
  have ha1 := hmin (-p.2) (-p.1 - p.2) (ha 1)
  have ha2 := hmin (-p.1) p.2 (ha 2)
  have hb0 := hmin (-p.1) (-p.1 + -p.2) (hb 0)
  have hb1 := hmin (-(-p.2)) (-(-p.1) - -p.2) (hb 1)
  have hb2 := hmin (-(-p.1)) (-p.2) (hb 2)
  have hxl : p.1 ≤ 0 := by
    rcases ha0 with h | h <;> rcases hb2 with h' | h' <;> linarith
  have hxr : 0 ≤ p.1 := by
    rcases hb0 with h | h <;> rcases ha2 with h' | h' <;> linarith
  apply Prod.ext
  · exact le_antisymm hxl hxr
  · change p.2 = 0
    rcases ha1 with h | h <;> rcases hb1 with h' | h' <;> linarith

/-- The coefficients are continuous across all sector boundaries. -/
theorem continuous_hexWeight : Continuous hexWeight := by
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp [hexWeight] <;> fun_prop

@[simp] theorem hexWeight_zero (j : Fin 3) : hexWeight 0 j = 0 := by
  fin_cases j <;> norm_num [hexWeight]

end VCDimConvexBound
