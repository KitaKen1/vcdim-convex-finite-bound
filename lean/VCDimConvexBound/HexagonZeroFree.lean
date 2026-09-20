import VCDimConvexBound.HexagonGenericZero
import VCDimConvexBound.SanyalSeparation
import VCDimConvexBound.ConvexCertificates

/-!
# Stability of configurations with no facet zero

Strict separation characterizes exclusion of zero from a finite convex hull.
The finitely many strict inequalities are open in the vertex images, so a
configuration without facet zeros remains so under small perturbations.
-/

namespace VCDimConvexBound

open scoped BigOperators Topology

theorem zero_not_mem_convexHull_range_iff_strict_positive {ι : Type*} [Fintype ι]
    {m : ℕ} (p : ι → Point m) :
    (0 : Point m) ∉ convexHull ℝ (Set.range p) ↔
      ∃ l : Point m →L[ℝ] ℝ, ∀ v, 0 < l (p v) := by
  constructor
  · intro h
    obtain ⟨l, u, hu, hl⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ _) ((Set.toFinite _).isClosed_convexHull ℝ) h
    refine ⟨l, fun v => ?_⟩
    simpa using hu.trans (hl _ (subset_convexHull ℝ _ (Set.mem_range_self v)))
  · rintro ⟨l, hl⟩ h
    have hs : convexHull ℝ (Set.range p) ⊆ {x | 0 < l x} := by
      apply convexHull_min _ (convex_halfSpace_gt ⟨l.map_add, l.map_smul⟩ 0)
      rintro _ ⟨v, rfl⟩
      exact hl v
    simpa using hs h

theorem isOpen_zero_not_mem_convexHull_range {ι : Type*} [Fintype ι] (m : ℕ) :
    IsOpen {p : ι → Point m | (0 : Point m) ∉ convexHull ℝ (Set.range p)} := by
  simp only [zero_not_mem_convexHull_range_iff_strict_positive,
    Set.ofPred_exists, Set.ofPred_forall]
  apply isOpen_iUnion
  intro l
  apply isOpen_iInter_of_finite
  intro v
  exact isOpen_lt continuous_const (l.continuous.comp (continuous_apply v))

/-- No maximal face has a nonnegative mass-one combination mapping to zero. -/
def HexZeroFree {r m : ℕ} (p : HexVertex r → Point m) : Prop :=
  ∀ s : Fin r → Fin 6,
    (0 : Point m) ∉ convexHull ℝ (Set.range (fun v : hexFacet s => p v.val))

theorem not_hexZeroFree_iff_barycentric_zero {r m : ℕ} (p : HexVertex r → Point m) :
    ¬ HexZeroFree p ↔ ∃ s : Fin r → Fin 6, ∃ x : (hexFacet s) → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v • p v.val) = 0 := by
  classical
  simp only [HexZeroFree, not_forall, not_not, mem_convexHull_range_iff_weights]
  aesop

theorem isOpen_hexZeroFree (r m : ℕ) :
    IsOpen {p : HexVertex r → Point m | HexZeroFree p} := by
  unfold HexZeroFree
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro s
  exact (isOpen_zero_not_mem_convexHull_range m).preimage
    (show Continuous (fun p : HexVertex r → Point m => fun v : hexFacet s => p v.val) by
      fun_prop)

/-- There is a uniform positive radius preserving exclusion of zero on every facet. -/
theorem HexZeroFree.exists_radius {r m : ℕ} {p : HexVertex r → Point m}
    (hp : HexZeroFree p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q, dist q p < ε → HexZeroFree q := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_hexZeroFree r m) p hp
  exact ⟨ε, hε, fun q hq => hball hq⟩

/-- The previously proved generic odd zero theorem rules out generic counterexamples. -/
theorem not_hexZeroFree_of_generic_odd {r : ℕ} (hr : 0 < r)
    (p : HexVertex r → Point (2 * r - 1))
    (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hG : HexFlagGeneric (hexFlagExtend p)) : ¬ HexZeroFree p :=
  (not_hexZeroFree_iff_barycentric_zero p).mpr
    (hexGenericOdd_exists_barycentric_zero hr p hp hG)

end VCDimConvexBound
