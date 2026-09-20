import VCDimConvexBound.SparseGenerators
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Strict supporting functionals for the Sanyal obstruction

For a finite configuration, convex independence is equivalent to a strict
linear supporting functional at each indexed point. For additive arrays,
the same functional must select the chosen point in every summand.
These are proved reductions, not a proof of the remaining obstruction.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Finite convex independence is witnessed by strict supporting functionals. -/
theorem convexIndependent_iff_strict_support {ι : Type*} [Fintype ι] {D : ℕ}
    (q : ι → Point D) :
    ConvexIndependent ℝ q ↔
      ∀ i, ∃ f : Point D →L[ℝ] ℝ, ∀ j, j ≠ i → f (q j) < f (q i) := by
  constructor
  · intro h i
    have hout : q i ∉ convexHull ℝ (q '' {j | j ≠ i}) := by
      intro hi
      exact h _ i hi rfl
    obtain ⟨f, u, hf, hui⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) ((Set.toFinite _).isClosed_convexHull ℝ) hout
    exact ⟨f, fun j hji => (hf _ (subset_convexHull ℝ _ ⟨j, hji, rfl⟩)).trans hui⟩
  · intro h s i hi
    by_contra his
    obtain ⟨f, hf⟩ := h i
    have hs : convexHull ℝ (q '' s) ⊆ {x | f x < f (q i)} := by
      apply convexHull_min _ (convex_halfSpace_lt ⟨f.map_add, f.map_smul⟩ _)
      rintro _ ⟨j, hj, rfl⟩
      exact hf j (fun hji => his (hji ▸ hj))
    exact (lt_irrefl (f (q i))) (hs hi)

/-- Convex independence of a finite configuration persists under small perturbations. -/
theorem isOpen_convexIndependent {ι : Type*} [Fintype ι] {D : ℕ} :
    IsOpen {q : ι → Point D | ConvexIndependent ℝ q} := by
  simp only [convexIndependent_iff_strict_support, Set.ofPred_forall, Set.ofPred_exists]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iUnion
  intro f
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt (f.continuous.comp (continuous_apply j))
    (f.continuous.comp (continuous_apply i))

/-- One linear functional strictly selects the prescribed point in every family. -/
def CommonStrictMaximizers {r m D : ℕ} (z : Fin r → Fin m → Point D) : Prop :=
  ∀ i : Grid r m, ∃ f : Point D →L[ℝ] ℝ,
    ∀ k j, j ≠ i k → f (z k j) < f (z k (i k))

/-- Changing one summand in an additive array. -/
theorem gridSum_update {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (i : Grid r m) (k : Fin r) (j : Fin m) :
    gridSum z (Function.update i k j) = gridSum z i - z k (i k) + z k j := by
  classical
  have he : (fun a => z a (Function.update i k j a)) =
      Function.update (fun a => z a (i a)) k (z k j) := by
    funext a
    by_cases ha : a = k <;> simp [ha]
  simp only [gridSum, he, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hs := Finset.sum_erase_add Finset.univ (fun a => z a (i a)) (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← hs]
  abel

/-- All sums are vertices exactly when every choice admits a common strict support. -/
theorem convexIndependent_gridSum_iff_commonStrictMaximizers {r m D : ℕ}
    (z : Fin r → Fin m → Point D) :
    ConvexIndependent ℝ (gridSum z) ↔ CommonStrictMaximizers z := by
  rw [convexIndependent_iff_strict_support]
  constructor
  · intro h i
    obtain ⟨f, hf⟩ := h i
    refine ⟨f, fun k j hji => ?_⟩
    have hne : Function.update i k j ≠ i := by
      intro he
      exact hji (by simpa using congrFun he k)
    have hlt := hf (Function.update i k j) hne
    rw [gridSum_update, map_add, map_sub] at hlt
    linarith
  · intro h i
    obtain ⟨f, hf⟩ := h i
    refine ⟨f, fun j hji => ?_⟩
    have hex : ∃ k, j k ≠ i k := Function.ne_iff.mp hji
    simp only [gridSum, map_sum]
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : j k = i k
      · simp [hk]
      · exact (hf k (j k) hk).le
    · obtain ⟨k, hk⟩ := hex
      exact ⟨k, Finset.mem_univ k, hf k (j k) hk⟩

/-- The set of counterexample arrays is open, including at degenerate configurations. -/
theorem isOpen_convexIndependent_gridSum (r m D : ℕ) :
    IsOpen {z : Fin r → Fin m → Point D | ConvexIndependent ℝ (gridSum z)} := by
  apply isOpen_convexIndependent.preimage
  unfold gridSum
  fun_prop

/-- The original geometric input is equivalent to failure of some common strict support. -/
theorem sanyalBoxObstruction_iff_no_commonStrictMaximizers (D : ℕ) :
    SanyalBoxObstruction D ↔
      ∀ z : Fin D → Fin (D + 1) → Point D, ¬ CommonStrictMaximizers z := by
  simp only [SanyalBoxObstruction, convexIndependent_gridSum_iff_commonStrictMaximizers]

end VCDimConvexBound
