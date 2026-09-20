import VCDimConvexBound.HexagonGenericTransport

/-!
# A barycentric zero for every odd vertex configuration

All determinant conditions are removed. If no facet had a zero, openness
would preserve that property under a small odd perturbation. The finite
minor family supplies a generic perturbation, contradicting the already
proved generic odd zero theorem.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Supply exactly HexFlagGeneric by an odd perturbation inside any specified
open neighborhood, retaining zero-freeness if it held initially. -/
theorem exists_odd_zeroFree_flagGeneric_perturbation {r : ℕ}
    (p : HexVertex r → Point (2 * r - 1))
    (hp : ∀ v, p (hexVertexOpposite v) = -p v) (hz : HexZeroFree p)
    (U : Set (HexVertex r → Point (2 * r - 1))) (hU : IsOpen U) (hpu : p ∈ U) :
    ∃ q : HexVertex r → Point (2 * r - 1),
      q ∈ U ∧ (∀ v, q (hexVertexOpposite v) = -q v) ∧
        HexZeroFree q ∧ HexFlagGeneric (hexFlagExtend q) := by
  obtain ⟨q, hq, hodd, hz', hG⟩ :=
    exists_odd_zeroFree_allMinors_perturbation p hp hz U hU hpu
  exact ⟨q, hq, hodd, hz', hG.flag⟩

/-- Every odd vertex configuration in dimension 2r-1 has a barycentric zero
on an actual maximal face. No general-position hypothesis remains. -/
theorem hexOdd_exists_barycentric_zero {r : ℕ} (hr : 0 < r)
    (p : HexVertex r → Point (2 * r - 1))
    (hp : ∀ v, p (hexVertexOpposite v) = -p v) :
    ∃ s : Fin r → Fin 6, ∃ x : (hexFacet s) → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v • p v.val) = 0 := by
  apply (not_hexZeroFree_iff_barycentric_zero p).mp
  intro hz
  obtain ⟨q, _, hodd, hz', hG⟩ :=
    exists_odd_zeroFree_flagGeneric_perturbation p hp hz Set.univ isOpen_univ (Set.mem_univ p)
  exact not_hexZeroFree_of_generic_odd hr q hodd hG hz'

end VCDimConvexBound
