import VCDimConvexBound.HexagonFlagCochains
import VCDimConvexBound.FlagBoundaryParity

/-!
# A barycentric zero for generic odd vertex configurations

The hypotheses below are concrete finite determinant conditions, not the
cochain identities to be proved. We derive those identities from the local
matrix theorems and then use the verified hemisphere tower. Removing the
determinant hypotheses remains a separate perturbation problem.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

/-- The finite general-position conditions used on the actual hexagon faces.
All enumerations are allowed; this makes the condition independent of choices.
Only coordinate heights strictly below 2r-1 occur. -/
structure HexFlagGeneric {r : ℕ} (p : HexVertex r → ℕ → ℝ) : Prop where
  boundary : ∀ k, k + 1 < 2 * r → ∀ f ∈ (hexFanComplex r).faces,
    ∀ e : Fin (k + 2) ≃ f,
      FlagSliceGeneric (hexFlagEnumMatrix p k e) (fun j => p (e j).val k)
  mass : ∀ k, k + 1 < 2 * r → ∀ f ∈ (hexFanComplex r).faces,
    ∀ e : Fin (k + 1) ≃ f,
      (flagPrependRow (fun _ => 1) (hexFlagEnumMatrix p k e)).det ≠ 0
  height : ∀ k, k + 1 < 2 * r → ∀ f ∈ (hexFanComplex r).faces,
    ∀ e : Fin (k + 1) ≃ f,
      (flagPrependRow (fun j => p (e j).val k) (hexFlagEnumMatrix p k e)).det ≠ 0

/-- The local matrix boundary formula is the actual face coboundary formula. -/
theorem hexFlag_boundary_parity {r k : ℕ} (p : HexVertex r → ℕ → ℝ)
    (f : Finset (HexVertex r)) (e : Fin (k + 2) ≃ f)
    (hG : FlagSliceGeneric (hexFlagEnumMatrix p k e) (fun j => p (e j).val k)) :
    hexFlagZero p (k + 1) f = hexCoboundary (hexFlagPositive p k) f := by
  rw [hexFlagZero_eq_enumeration p (k + 1) f e, hexFlagEnumMatrix_succ,
    flag_local_boundary_parity _ _ hG, hexCoboundary_eq_sum_enumeration _ f e]
  apply Finset.sum_congr rfl
  intro i _
  exact (hexFlagPositive_erase p k e i).symm

/-- Oddness of the vertex images turns matrix negation into the actual antipode. -/
theorem hexFlag_antipodal_parity {r k : ℕ} (p : HexVertex r → ℕ → ℝ)
    (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j)
    (f : Finset (HexVertex r)) (e : Fin (k + 1) ≃ f)
    (hmass : (flagPrependRow (fun _ => 1) (hexFlagEnumMatrix p k e)).det ≠ 0)
    (hheight : (flagPrependRow (fun j => p (e j).val k)
      (hexFlagEnumMatrix p k e)).det ≠ 0) :
    hexFlagZero p k f = hexFlagPositive p k f +
      hexAntipodalCochain (hexFlagPositive p k) f := by
  have hn : flagPositiveBit (-hexFlagEnumMatrix p k e) (-(fun j => p (e j).val k)) =
      hexFlagPositive p k (f.image hexVertexOpposite) := by
    rw [hexFlagPositive_antipodal p hp]
    exact flagPositiveBit_reindex (-hexFlagMatrix p k f) (fun v => -p v.val k) e
  rw [hexFlagZero_eq_enumeration p k f e,
    flag_antipodal_crossing_parity _ _ hmass hheight, hn,
    ← hexFlagPositive_eq_enumeration p k f e]
  rfl

/-- Supply the boundary input of the tower from the stated determinant conditions. -/
theorem HexFlagGeneric.boundary_identity {r : ℕ} {p : HexVertex r → ℕ → ℝ}
    (hG : HexFlagGeneric p) (k : ℕ) (hk : k + 1 < 2 * r)
    (f : Finset (HexVertex r)) (hf : f ∈ (hexFanComplex r).faces) (hcard : f.card = k + 2) :
    hexFlagZero p (k + 1) f = hexCoboundary (hexFlagPositive p k) f :=
  hexFlag_boundary_parity p f (hexFaceEnumeration f hcard)
    (hG.boundary k hk f hf (hexFaceEnumeration f hcard))

/-- Supply the antipodal input of the tower from oddness and nonzero determinants. -/
theorem HexFlagGeneric.antipodal_identity {r : ℕ} {p : HexVertex r → ℕ → ℝ}
    (hG : HexFlagGeneric p) (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j)
    (k : ℕ) (hk : k + 1 < 2 * r) (f : Finset (HexVertex r))
    (hf : f ∈ (hexFanComplex r).faces) (hcard : f.card = k + 1) :
    hexFlagZero p k f = hexFlagPositive p k f +
      hexAntipodalCochain (hexFlagPositive p k) f :=
  hexFlag_antipodal_parity p hp f (hexFaceEnumeration f hcard)
    (hG.mass k hk f hf (hexFaceEnumeration f hcard))
    (hG.height k hk f hf (hexFaceEnumeration f hcard))

/-- The geometric crossing cochain evaluates to one in every degree of the tower. -/
theorem hexFlagGeneric_parity_one {r : ℕ} (p : HexVertex r → ℕ → ℝ)
    (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j) (hG : HexFlagGeneric p)
    {k : ℕ} (hk : k < 2 * r) :
    hexCochainEval (hexFlagZero p k) (hexHemisphereTower r k) = 1 :=
  hexHemisphereTower_parity_one (hexFlagZero p) (hexFlagPositive p)
    (hexFlagZero_vertex p) hG.boundary_identity (hG.antipodal_identity hp) hk

/-- An actual facet has a nonnegative mass-one zero of all first 2r-1 coordinates. -/
theorem hexFlagGeneric_exists_zero {r : ℕ} (hr : 0 < r) (p : HexVertex r → ℕ → ℝ)
    (hp : ∀ v j, p (hexVertexOpposite v) j = -p v j) (hG : HexFlagGeneric p) :
    ∃ s : Fin r → Fin 6, ∃ x : (hexFacet s) → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧
        ∀ j : Fin (2 * r - 1), (∑ v, x v * p v.val j.val) = 0 := by
  obtain ⟨s, hs⟩ := hexHemisphereTower_exists_top_crossing hr
    (hexFlagZero p) (hexFlagPositive p) (hexFlagZero_vertex p)
    hG.boundary_identity (hG.antipodal_identity hp)
  exact ⟨s, (hexFlagZero_ne_zero_iff p _ _).mp hs⟩

/-- Extend a finite-dimensional vertex image by zero; used only to index prefixes. -/
def hexFlagExtend {r m : ℕ} (p : HexVertex r → Fin m → ℝ) : HexVertex r → ℕ → ℝ :=
  fun v j => if h : j < m then p v ⟨j, h⟩ else 0

theorem hexFlagExtend_odd {r m : ℕ} (p : HexVertex r → Fin m → ℝ)
    (hp : ∀ v, p (hexVertexOpposite v) = -p v) :
    ∀ v j, hexFlagExtend p (hexVertexOpposite v) j = -hexFlagExtend p v j := by
  intro v j
  simp only [hexFlagExtend]
  split_ifs with h
  · exact congrFun (hp v) ⟨j, h⟩
  · simp

/-- In the actual target dimension, a generic odd vertex configuration has zero
in the convex hull of the image of some actual facet. -/
theorem hexGenericOdd_exists_barycentric_zero {r : ℕ} (hr : 0 < r)
    (p : HexVertex r → Fin (2 * r - 1) → ℝ)
    (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hG : HexFlagGeneric (hexFlagExtend p)) :
    ∃ s : Fin r → Fin 6, ∃ x : (hexFacet s) → ℝ,
      (∑ v, x v) = 1 ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v • p v.val) = 0 := by
  obtain ⟨s, x, hm, hx, hz⟩ :=
    hexFlagGeneric_exists_zero hr (hexFlagExtend p) (hexFlagExtend_odd p hp) hG
  refine ⟨s, x, hm, hx, ?_⟩
  funext j
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hexFlagExtend, j.isLt] using hz j

end VCDimConvexBound
