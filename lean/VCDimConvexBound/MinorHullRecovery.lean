import VCDimConvexBound.MinorIndependence
import VCDimConvexBound.Minors

/-!
# All-minor signs determine finite convex-hull membership

Choose a positive independent certificate, restrict to a nonsingular row
minor, and transfer the signs of its Cramer coefficients. The other rows are
handled by preservation of span membership, itself certified by all minors.
Thus no full-dimensionality or general-position hypothesis is needed.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

theorem submatrix_updateCol {ρ ι κ : Type*} [DecidableEq κ]
    (A : Matrix ρ ι ℝ) (r : κ → ρ) (c : κ → ι) (j : κ) (i : ι) :
    (A.submatrix r c).updateCol j (fun a => A (r a) i) =
      A.submatrix r (Function.update c j i) := by
  ext a b
  by_cases h : b = j <;> simp [Matrix.submatrix, h]

/-- Transfer a nonnegative linear certificate on an independent support. -/
theorem SameMinorSigns.nonnegative_certificate {ρ ι κ : Type*}
    [Fintype ρ] [Fintype κ] {A B : Matrix ρ ι ℝ}
    (h : SameMinorSigns A B) (c : κ → ι) (i : ι)
    (hA : LinearIndependent ℝ (fun j => A.col (c j)))
    (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (he : ∑ j, w j • A.col (c j) = A.col i) :
    ∃ v : κ → ℝ, (∀ j, 0 ≤ v j) ∧ ∑ j, v j • B.col (c j) = B.col i := by
  classical
  have hspan : A.col i ∈ Submodule.span ℝ (Set.range (fun j => A.col (c j))) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨w, he⟩
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    ((h.mem_span_iff c hA i).mp hspan)
  obtain ⟨r, hr⟩ := exists_nonsingular_row_restriction (A.submatrix id c) hA
  have ha : (A.submatrix r c).det ≠ 0 := by simpa using hr
  have hd := h.det_submatrix r c
  have hb : (B.submatrix r c).det ≠ 0 :=
    fun hb => ha (((signCode_eq_iff _ _).mp hd).2.mpr hb)
  have hwa : A.submatrix r c *ᵥ w = fun a => A (r a) i := by
    ext a
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix, Matrix.col,
      Finset.sum_apply, mul_comm] using congrFun he (r a)
  have hvb : B.submatrix r c *ᵥ v = fun a => B (r a) i := by
    ext a
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix, Matrix.col,
      Finset.sum_apply, mul_comm] using congrFun hv (r a)
  have hca := cramerWeights_eq_of_mulVec _ _ _ ha hwa
  have hcb := cramerWeights_eq_of_mulVec _ _ _ hb hvb
  have hn := cramerWeights_nonneg_iff (A.submatrix r c) (B.submatrix r c)
    (fun a => A (r a) i) (fun a => B (r a) i) hd
    (fun j => by simpa only [submatrix_updateCol] using
      h.det_submatrix r (Function.update c j i))
  rw [hca, hcb] at hn
  exact ⟨v, hn.mp hw, hv⟩

/-- Augmented columns of an arbitrary indexed configuration. -/
def augmentedMatrix {ι : Type*} {D : ℕ} (q : ι → Point D) :
    Matrix (Option (Fin D)) ι ℝ := Matrix.of fun r i => augmentedPoint (q i) r

/-- Equal all-minor signs transfer convex membership, including degenerate configurations. -/
theorem mem_indexedHull_of_sameMinorSigns {ι : Type*} {D : ℕ}
    (q q' : ι → Point D) (h : SameMinorSigns (augmentedMatrix q) (augmentedMatrix q'))
    (V : Finset ι) (i : ι) (hi : q i ∈ indexedHull q V) :
    q' i ∈ indexedHull q' V := by
  obtain ⟨r, c, w, _, _, hc, _, hl, hw, he⟩ := exists_independent_convexCertificate q V hi
  obtain ⟨v, hv, he'⟩ := h.nonnegative_certificate c i hl w (fun j => (hw j).le) he
  have hcoords := (sum_smul_augmentedPoint_eq_iff (fun j => q' (c j)) v (q' i)).mp he'
  exact mem_convexHull_of_exists_fintype v (fun j => q' (c j)) hv hcoords.1
    (fun j => ⟨c j, hc j, rfl⟩) hcoords.2

theorem mem_indexedHull_iff_of_sameMinorSigns {ι : Type*} {D : ℕ}
    (q q' : ι → Point D) (h : SameMinorSigns (augmentedMatrix q) (augmentedMatrix q'))
    (V : Finset ι) (i : ι) :
    q i ∈ indexedHull q V ↔ q' i ∈ indexedHull q' V :=
  ⟨mem_indexedHull_of_sameMinorSigns q q' h V i,
    mem_indexedHull_of_sameMinorSigns q' q h.symm V i⟩

/-- The polynomial family from P5 uses exactly the row-subset minor encoding above. -/
theorem sameMinorSigns_of_polynomial_signs {D m : ℕ}
    (z z' : Fin D → Fin m → Point D)
    (h : ∀ j : MinorIndex D m,
      signCode (MvPolynomial.eval (arrayAssignment z) (minorPolynomial j)) =
      signCode (MvPolynomial.eval (arrayAssignment z') (minorPolynomial j))) :
    SameMinorSigns (augmentedMatrix (gridSum z)) (augmentedMatrix (gridSum z')) := by
  classical
  intro R c
  have hdet (d : DecidableEq R) :
      @Matrix.det R d inferInstance ℝ inferInstance =
        @Matrix.det R (Classical.decEq R) inferInstance ℝ inferInstance :=
    congrArg (fun d => @Matrix.det R d inferInstance ℝ inferInstance) (Subsingleton.elim _ _)
  have hp := h ⟨R, c⟩
  simp only [eval_minorPolynomial, hdet] at hp
  simpa only [augmentedMatrix, augmentedPoint, Matrix.submatrix, Matrix.of_apply, hdet] using hp

/-- P5: the signs of all encoded polynomial minors determine every finite hull label. -/
theorem same_signs_same_hull_membership {D m : ℕ}
    (z z' : Fin D → Fin m → Point D)
    (h : ∀ j : MinorIndex D m,
      signCode (MvPolynomial.eval (arrayAssignment z) (minorPolynomial j)) =
      signCode (MvPolynomial.eval (arrayAssignment z') (minorPolynomial j)))
    (V : Finset (Grid D m)) (i : Grid D m) :
    gridSum z i ∈ indexedHull (gridSum z) V ↔
      gridSum z' i ∈ indexedHull (gridSum z') V :=
  mem_indexedHull_iff_of_sameMinorSigns _ _ (sameMinorSigns_of_polynomial_signs z z' h) V i

end VCDimConvexBound
