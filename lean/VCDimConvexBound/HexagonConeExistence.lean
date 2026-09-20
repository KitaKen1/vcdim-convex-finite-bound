import VCDimConvexBound.HexagonOddZero
import VCDimConvexBound.HexagonVertexBridge
import VCDimConvexBound.HexagonConeCore

/-!
# Proof of the geometric cone-kernel core

Transport actual vertex images in the Cayley color-sum kernel to R^(2D-1).
The unconditional odd vertex theorem supplies a barycentric zero. The
sector interpolation bridge turns it into the normalized nonnegative
kernel certificate. The original VC bound now needs only the independent
hypersurface component bound.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Every actual hexagon map has a normalized nonnegative piece-kernel
certificate. No convex-independence or general-position assumption is used. -/
theorem hexagon_exists_normalized_piece_kernel (D : ℕ) (hD : 0 < D)
    (z : Fin D → Fin 3 → Point D) :
    ∃ s : Fin D → Fin 6, ∃ t : HexagonDomain D,
      HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0 := by
  let E : LinearMap.ker (cayleyColorSum D D) ≃ₗ[ℝ] Point (2 * D - 1) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [finrank_ker_cayleyColorSum D hD, Point])
  let p : HexVertex D → Point (2 * D - 1) :=
    fun v => E (hexagonKernelMap hD z (hexDomainVertex v))
  have hp : ∀ v, p (hexVertexOpposite v) = -p v := by
    intro v
    dsimp [p]
    rw [hexDomainVertex_opposite, hexagonKernelMap_neg, map_neg]
  obtain ⟨s, x, hm, hx, hz⟩ := hexOdd_exists_barycentric_zero hD p hp
  have hk : (∑ v : hexFacet s, x v • hexagonKernelMap hD z (hexDomainVertex v.val)) = 0 := by
    apply E.injective
    simpa only [map_sum, map_smul, map_zero] using hz
  have ha : (∑ v : hexFacet s, x v • hexagonCayleyMap z (hexDomainVertex v.val)) = 0 := by
    have he := congrArg Subtype.val hk
    simpa [hexagonKernelMap] using he
  exact ⟨s, exists_hexPiece_kernel_of_facet_zero z s x hm hx ha⟩

/-- The previously isolated geometric core is now proved. -/
theorem hexConeKernelCore : HexConeKernelCore := by
  intro D hD z
  exact hexagon_exists_normalized_piece_kernel D (by omega) z

/-- Sanyal's required box obstruction, with no geometric core hypothesis. -/
theorem sanyalBoxObstruction (D : ℕ) (hD : 2 ≤ D) : SanyalBoxObstruction D :=
  sanyalBoxObstruction_of_hexConeKernel hexConeKernelCore D hD

/-- The original explicit VC bound now has only the hypersurface component
bound as an unproved input. -/
theorem explicit_bound_of_hypersurface (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) :=
  explicit_bound_of_hexConeKernel_hypersurface hexConeKernelCore hM n hn C hC

/-- The FC existence conclusion, conditional only on the component bound. -/
theorem exists_bound_of_hypersurface (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d :=
  exists_bound_of_hexConeKernel_hypersurface hexConeKernelCore hM n hn

end VCDimConvexBound
