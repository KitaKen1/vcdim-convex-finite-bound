import VCDimConvexBound.HexagonChainSupport

/-!
# The full graded hemisphere tower

For r colors and 0 ≤ k < 2r, the chain c_k has k+1 vertices per face.
The two new top chains are a half-cycle join and a cone; lower chains are
embedded in the old colors. This gives ∂c_(k+1) = c_k + A c_k in every degree.
-/

namespace VCDimConvexBound

/-- All degrees of the hemisphere construction, in one fixed ambient complex. -/
noncomputable def hexHemisphereTower : (r : ℕ) → ℕ → HexModTwoChain r
  | 0, _ => 0
  | r + 1, k =>
    if k = 2 * r + 1 then hexHemisphereChain r
    else if k = 2 * r then hexConeChain r 0
    else hexPrependChain ∅ (hexHemisphereTower r k)

theorem hexHemisphereTower_top (r : ℕ) :
    hexHemisphereTower (r + 1) (2 * r + 1) = hexHemisphereChain r := by
  simp [hexHemisphereTower]

theorem hexHemisphereTower_cone (r : ℕ) :
    hexHemisphereTower (r + 1) (2 * r) = hexConeChain r 0 := by
  simp [hexHemisphereTower]

theorem hexHemisphereTower_lower {r k : ℕ} (hk : k < 2 * r) :
    hexHemisphereTower (r + 1) k = hexPrependChain ∅ (hexHemisphereTower r k) := by
  rw [hexHemisphereTower, if_neg (by omega), if_neg (by omega)]

theorem hexHemisphereTower_full {r : ℕ} (hr : 0 < r) :
    hexFundamentalChain r = hexHemisphereTower r (2 * r - 1) +
      hexAntipodalChain r (hexHemisphereTower r (2 * r - 1)) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [show 2 * (s + 1) - 1 = 2 * s + 1 by omega, hexHemisphereTower_top]
  exact hexFundamentalChain_eq_hemisphere_add_antipodal s

/-- The actual deletion boundary satisfies the tower recursion in all degrees. -/
theorem hexHemisphereTower_boundary {r k : ℕ} (hk : k + 1 < 2 * r) :
    hexChainBoundary r (hexHemisphereTower r (k + 1)) =
      hexHemisphereTower r k + hexAntipodalChain r (hexHemisphereTower r k) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases htop : k + 1 = 2 * r + 1
    · have he : k = 2 * r := by omega
      subst k
      rw [hexHemisphereTower_top, hexHemisphereTower_cone]
      exact hexHemisphereChain_boundary_antipodal r
    by_cases hcone : k + 1 = 2 * r
    · have hr : 0 < r := by omega
      have he : k = 2 * r - 1 := by omega
      rw [hcone, hexHemisphereTower_cone, hexConeChain_boundary,
        hexHemisphereTower_lower (by omega), he, hexHemisphereTower_full hr,
        map_add, hexAntipodalChain_prepend]
      simp
    · have hlow : k + 1 < 2 * r := by omega
      rw [hexHemisphereTower_lower hlow, hexHemisphereTower_lower (by omega),
        hexChainBoundary_prepend, ih hlow, map_add, hexAntipodalChain_prepend]
      simp

/-- Every tower coefficient is supported on a face of exactly the required degree. -/
theorem hexHemisphereTower_onFaces {r k : ℕ} (hk : k < 2 * r) :
    HexChainOnFaces (k + 1) (hexHemisphereTower r k) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases htop : k = 2 * r + 1
    · subst k
      rw [hexHemisphereTower_top]
      exact hexHemisphereChain_onFaces r
    by_cases hcone : k = 2 * r
    · subst k
      rw [hexHemisphereTower_cone]
      exact hexConeChain_onFaces r 0
    · have hlow : k < 2 * r := by omega
      rw [hexHemisphereTower_lower hlow]
      simpa using (ih hlow).prepend ∅ ⟨0, Finset.empty_subset _⟩

/-- In degree zero the tower consists of one actual vertex, in the last color. -/
theorem hexHemisphereTower_base (r : ℕ) :
    hexHemisphereTower (r + 1) 0 = hexFaceBasis {(Fin.last r, 0)} := by
  induction r with
  | zero =>
    rw [show 0 = 2 * 0 from rfl, hexHemisphereTower_cone]
    simp [hexConeChain, hexFundamentalChain, hexFacet, hexPrependChain_basis,
      hexJoinFace, hexHeadVertex]
  | succ r ih =>
    rw [hexHemisphereTower_lower (by omega), ih, hexPrependChain_basis]
    simp [hexJoinFace, hexTailVertex]

end VCDimConvexBound
