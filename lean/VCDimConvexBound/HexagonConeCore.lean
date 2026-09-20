import VCDimConvexBound.HexagonLinearPieces
import VCDimConvexBound.SanyalOddMap

/-!
# A finite cone-kernel input sufficient for the original bound

Only the specific linear pieces of the hexagon map need a nonnegative kernel
certificate. This is weaker than the general odd-map zero principle. The
existence of such a certificate for every configuration remains unproved.
-/

namespace VCDimConvexBound

/-- The remaining geometric input, expressed using finitely many linear systems.
For each configuration, at least one of the `6^D` pieces must have a nonnegative
kernel vector of total mass one. This definition is not a proof. -/
def HexConeKernelCore : Prop :=
  ∀ (D : ℕ), 2 ≤ D → ∀ z : Fin D → Fin 3 → Point D,
    ∃ s : Fin D → Fin 6, ∃ t : HexagonDomain D,
      HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0

/-- The general odd-map principle supplies the specialized cone certificate. -/
theorem hexConeKernelCore_of_oddMapZero (hB : OddMapZeroCore) : HexConeKernelCore := by
  intro D hD z
  have hD' : 0 < D := by omega
  obtain ⟨x, hx, hf⟩ := hB D hD' (hexagonKernelMap hD' z)
    (continuous_hexagonKernelMap hD' z) (hexagonKernelMap_neg hD' z)
  apply (hexagon_zero_iff_normalized_piece_kernel z).mp
  exact ⟨x, hx, congrArg Subtype.val hf⟩

/-- A specialized nonnegative certificate already contradicts convex independence. -/
theorem not_convexIndependent_three_of_hexConeKernel (hK : HexConeKernelCore)
    (D : ℕ) (hD : 2 ≤ D) (z : Fin D → Fin 3 → Point D) :
    ¬ ConvexIndependent ℝ (gridSum z) := by
  intro hz
  obtain ⟨x, hx, hf⟩ := (hexagon_zero_iff_normalized_piece_kernel z).mpr (hK D hD z)
  exact hexagonCayleyMap_ne_zero (by omega) z hz x hx hf

/-- Restricting to three choices connects the cone certificate to Sanyal. -/
theorem sanyalBoxObstruction_of_hexConeKernel (hK : HexConeKernelCore)
    (D : ℕ) (hD : 2 ≤ D) : SanyalBoxObstruction D := by
  intro z hz
  let e : Fin 3 ↪ Fin (D + 1) :=
    ⟨Fin.castLE (by omega), Fin.castLE_injective (by omega)⟩
  exact not_convexIndependent_three_of_hexConeKernel hK D hD
    (fun k j => z k (e j)) (convexIndependent_gridSum_restrict z hz e)

/-- The original explicit bound needs only the cone and hypersurface cores. -/
theorem explicit_bound_of_hexConeKernel_hypersurface
    (hK : HexConeKernelCore) (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) :=
  explicit_bound_of_sanyal_hypersurface n hn
    (sanyalBoxObstruction_of_hexConeKernel hK (n + 1) (by omega)) hM C hC

/-- The FC existence conclusion with the specialized geometric input. -/
theorem exists_bound_of_hexConeKernel_hypersurface
    (hK : HexConeKernelCore) (hM : HypersurfaceComponentBound) (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d :=
  ⟨bound n, fun C hC => explicit_bound_of_hexConeKernel_hypersurface hK hM n hn C hC⟩

end VCDimConvexBound
