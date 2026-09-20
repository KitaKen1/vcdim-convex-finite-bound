import VCDimConvexBound.SanyalGale

/-!
# Dimension of the projection-kernel configuration

Record row sums together with the weighted image. If one point family is a
full-dimensional simplex, this linear map is onto. Rank-nullity then gives
r(D+1) - (r+D) dimensions for the kernel, or D²-D for r=D.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The linear map recording row masses and the weighted point sum. -/
def cayleyMap {r m D : ℕ} (z : Fin r → Fin m → Point D) :
    ((Fin r × Fin m) → ℝ) →ₗ[ℝ] ((Fin r → ℝ) × Point D) where
  toFun x := (fun k => ∑ j, x (k, j), ∑ e, x e • z e.1 e.2)
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib, add_smul]
  map_smul' a x := by
    ext <;> simp [Finset.mul_sum, mul_smul]

/-- The barycentric kernel is the ordinary kernel of the Cayley linear map. -/
theorem ker_cayleyMap {r m D : ℕ} (z : Fin r → Fin m → Point D) :
    LinearMap.ker (cayleyMap z) = cayleyKernel z := by
  ext x
  simp [LinearMap.mem_ker, cayleyMap, cayleyKernel, Prod.ext_iff, funext_iff]

@[simp] theorem cayleyMap_single {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (e : Fin r × Fin m) :
    cayleyMap z (Pi.single e 1) = (Pi.single e.1 1, z e.1 e.2) := by
  classical
  apply Prod.ext
  · funext k
    change (∑ j, (Pi.single e 1 : (Fin r × Fin m) → ℝ) (k, j)) =
      (Pi.single e.1 1 : Fin r → ℝ) k
    by_cases h : k = e.1
    · subst k
      simp [Pi.single_apply, Prod.ext_iff]
    · simp [Prod.ext_iff, h]
  · change (∑ a, (Pi.single e 1 : (Fin r × Fin m) → ℝ) a • z a.1 a.2) = z e.1 e.2
    simp [Pi.single_apply]

/-- Edge vectors from the base vertex of a full-dimensional simplex span the ambient space. -/
theorem span_simplex_edges_eq_top {D : ℕ} (q : Fin (D + 1) → Point D)
    (hq : AffineIndependent ℝ q) :
    Submodule.span ℝ (Set.range (fun j : Fin D => q j.succ - q 0)) = ⊤ := by
  have hl := (affineIndependent_iff_linearIndependent_vsub ℝ q 0).mp hq
  have he : LinearIndependent ℝ (fun j : Fin D => q j.succ - q 0) := by
    simpa [Function.comp_def, finSuccAboveEquiv_apply] using!
      (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (D + 1)))).mpr hl
  exact he.span_eq_top_of_card_eq_finrank' (by simp [Point])

/-- One simplex family suffices to make the Cayley map surjective. -/
theorem range_cayleyMap_eq_top_of_simplex {r D : ℕ}
    (z : Fin r → Fin (D + 1) → Point D) (k : Fin r)
    (hk : AffineIndependent ℝ (z k)) :
    LinearMap.range (cayleyMap z) = ⊤ := by
  classical
  let K := LinearMap.range (cayleyMap z)
  have hedge (j : Fin D) : (0, z k j.succ - z k 0) ∈ K := by
    refine ⟨Pi.single (k, j.succ) 1 - Pi.single (k, 0) 1, ?_⟩
    rw [map_sub, cayleyMap_single, cayleyMap_single]
    simp
  have hspan : Submodule.span ℝ (Set.range (fun j : Fin D => z k j.succ - z k 0)) ≤
      K.comap (LinearMap.inr ℝ (Fin r → ℝ) (Point D)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hedge j
  rw [span_simplex_edges_eq_top (z k) hk] at hspan
  have hzero (y : Point D) : (0, y) ∈ K := hspan (Submodule.mem_top)
  apply top_unique
  rintro ⟨a, y⟩ _
  have hbase : (a, ∑ l, a l • z l 0) ∈ K := by
    refine ⟨fun e => if e.2 = 0 then a e.1 else 0, ?_⟩
    apply Prod.ext
    · funext l
      simp [cayleyMap]
    · change (∑ e : Fin r × Fin (D + 1),
        (if e.2 = 0 then a e.1 else 0) • z e.1 e.2) = _
      rw [Fintype.sum_prod_type]
      simp
  have h := K.add_mem hbase (hzero (y - ∑ l, a l • z l 0))
  simpa [K] using h

/-- Exact rank-nullity, without truncated-subtraction side conditions. -/
theorem finrank_cayleyKernel_add {r D : ℕ}
    (z : Fin r → Fin (D + 1) → Point D) (k : Fin r)
    (hk : AffineIndependent ℝ (z k)) :
    Module.finrank ℝ (cayleyKernel z) + (r + D) = r * (D + 1) := by
  have h := (cayleyMap z).finrank_range_add_finrank_ker
  rw [ker_cayleyMap, range_cayleyMap_eq_top_of_simplex z k hk] at h
  simpa [Module.finrank_prod, Point, Nat.add_comm] using h

/-- The kernel-dual configuration for D simplices lives in dimension D²-D. -/
theorem finrank_galeSpace {D : ℕ} (hD : 0 < D)
    (z : Fin D → Fin (D + 1) → Point D)
    (hz : ∀ k, AffineIndependent ℝ (z k)) :
    Module.finrank ℝ (Module.Dual ℝ (cayleyKernel z)) = D * (D - 1) := by
  rw [Subspace.dual_finrank_eq]
  have h := finrank_cayleyKernel_add z ⟨0, hD⟩ (hz ⟨0, hD⟩)
  have hd : D - 1 + 1 = D := Nat.sub_add_cancel hD
  nlinarith

end VCDimConvexBound
