import VCDimConvexBound.HexagonMap
import VCDimConvexBound.MilnorConditionalBound

/-!
# Reduction of Sanyal to a precise odd-map zero principle

The continuous odd map is now constructed. Only its topological obstruction
is an unproved input. This input is a proposition passed as an argument,
not a new axiom. Together with the hypersurface component bound it yields
the original explicit VC bound.
-/

namespace VCDimConvexBound

/-- The remaining Borsuk-Ulam-type input, in exactly the spaces used here.
The domain has dimension 2D and the target has dimension 2D-1. This definition
is not a proof of the principle. The zero must occur away from the origin. -/
def OddMapZeroCore : Prop :=
  ∀ (D : ℕ), 0 < D →
    ∀ f : HexagonDomain D → LinearMap.ker (cayleyColorSum D D),
      Continuous f → (∀ x, f (-x) = -f x) → ∃ x, x ≠ 0 ∧ f x = 0

/-- Restricting the choices in each color preserves convex independence of all sums. -/
theorem convexIndependent_gridSum_restrict {r m m' D : ℕ}
    (z : Fin r → Fin m' → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (e : Fin m ↪ Fin m') :
    ConvexIndependent ℝ (gridSum (fun k j => z k (e j))) := by
  let E : Grid r m ↪ Grid r m' :=
    ⟨fun i k => e (i k), fun a b h => funext (fun k => e.injective (congrFun h k))⟩
  exact hz.comp_embedding E

/-- Three choices per color contradict the odd-map zero principle. -/
theorem not_convexIndependent_three_of_oddMapZero (hB : OddMapZeroCore)
    (D : ℕ) (hD : 0 < D) (z : Fin D → Fin 3 → Point D) :
    ¬ ConvexIndependent ℝ (gridSum z) := by
  intro hz
  obtain ⟨x, hx, hf⟩ := hB D hD (hexagonKernelMap hD z)
    (continuous_hexagonKernelMap hD z) (hexagonKernelMap_neg hD z)
  exact hexagonKernelMap_ne_zero hD z hz x hx hf

/-- Restrict a putative Sanyal counterexample to three points per color. -/
theorem sanyalBoxObstruction_of_oddMapZero (hB : OddMapZeroCore)
    (D : ℕ) (hD : 2 ≤ D) : SanyalBoxObstruction D := by
  intro z hz
  let e : Fin 3 ↪ Fin (D + 1) :=
    ⟨Fin.castLE (by omega), Fin.castLE_injective (by omega)⟩
  exact not_convexIndependent_three_of_oddMapZero hB D (by omega)
    (fun k j => z k (e j)) (convexIndependent_gridSum_restrict z hz e)

/-- The original bound, now with the two remaining cores stated directly. -/
theorem explicit_bound_of_oddMapZero_hypersurface
    (hB : OddMapZeroCore) (hM : HypersurfaceComponentBound)
    (n : ℕ) (hn : 1 ≤ n) (C : Set (Point (n + 1))) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (bound n) :=
  explicit_bound_of_sanyal_hypersurface n hn
    (sanyalBoxObstruction_of_oddMapZero hB (n + 1) (by omega)) hM C hC

/-- The FC existence conclusion retains only the odd-map and component inputs. -/
theorem exists_bound_of_oddMapZero_hypersurface
    (hB : OddMapZeroCore) (hM : HypersurfaceComponentBound) (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d :=
  ⟨bound n, fun C hC => explicit_bound_of_oddMapZero_hypersurface hB hM n hn C hC⟩

end VCDimConvexBound
