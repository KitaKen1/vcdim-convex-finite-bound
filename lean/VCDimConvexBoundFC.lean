import FormalConjectures.Other.VCDimConvex
import VCDimConvexBound.FCStatement

/-!
# A finite additive VC_n bound for convex sets

This file imports the pinned Formal Conjectures target and the local proof.
The theorem below repeats the target's complete binders and conclusion and
discharges it using the explicit bound proved in `VCDimConvexBound.FinalBound`.
-/

namespace VCDimConvexBoundFC

/-- The exact uniform finite-bound existence target registered in Formal Conjectures. -/
theorem vcdim_convex_uniform_bound_solved (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d :=
  VCDimConvexBound.fc_exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one n hn

#check VCDimConvex.exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one
#check VCDimConvexBound.explicit_bound
#check vcdim_convex_uniform_bound_solved
#print axioms VCDimConvexBound.explicit_bound
#print axioms vcdim_convex_uniform_bound_solved

end VCDimConvexBoundFC
