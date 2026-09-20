import VCDimConvexBound.HexagonOddFaceExtension

/-!
# Nonzero determinant polynomials in the odd configuration parameters

Rows select distinct coordinates, with an optional constant mass row.
Columns select every vertex of a finite set containing no antipodal pair.
Arbitrary face data supply an explicit determinant-one evaluation, so these
polynomials are genuinely nonzero even with the global oddness constraint.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix

/-- Replacing one row of the identity by all ones still has determinant one. -/
theorem det_identity_updateRow_ones {n : ℕ} (i : Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun _ => 1)).det = 1 := by
  have hs : (∑ j : Fin n, (1 : Matrix (Fin n) (Fin n) ℝ) j) =
      (fun _ => 1) := by
    funext k
    change (∑ j : Fin n, fun l : Fin n => if j = l then (1 : ℝ) else 0) k = 1
    simp [Finset.sum_apply]
  simpa only [one_smul, hs, Matrix.det_one] using
    Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) ℝ) i (fun _ => 1)

/-- Prescribe a square matrix whose selected constant row is already all ones. -/
theorem exists_hexOddParameters_augmented_face_matrix {r m n : ℕ}
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i, ρ i = none → ∀ j, M i j = 1) :
    ∃ a : HexOddVariable r m → ℝ,
      ∀ i j, (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l) = M i j := by
  let b : f → Point m := fun v l =>
    Function.extend ρ (fun i => M i (e.symm v)) 0 (some l)
  obtain ⟨a, ha⟩ := exists_hexOddParameters_agree_on_face f hf b
  refine ⟨a, fun i j => ?_⟩
  cases hi : ρ i with
  | none => exact (hM i hi j).symm
  | some l =>
    simp only [Option.elim_some]
    rw [ha (e j)]
    change Function.extend ρ (fun i => M i (e.symm (e j))) 0 (some l) = M i j
    rw [← hi, ρ.injective.extend_apply, e.symm_apply_apply]

/-- Every augmented minor pattern has a determinant-one realization by odd data. -/
theorem exists_hexOddParameters_augmented_det_one {r m n : ℕ}
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)) :
    ∃ a : HexOddVariable r m → ℝ,
      (Matrix.of (fun i j => (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l))).det = 1 := by
  classical
  by_cases hnone : ∃ i, ρ i = none
  · obtain ⟨i₀, hi₀⟩ := hnone
    let M : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i₀ (fun _ => 1)
    have hM : ∀ i, ρ i = none → ∀ j, M i j = 1 := by
      intro i hi j
      have he : i = i₀ := ρ.injective (hi.trans hi₀.symm)
      subst i
      simp [M]
    obtain ⟨a, ha⟩ := exists_hexOddParameters_augmented_face_matrix f hf e ρ M hM
    refine ⟨a, ?_⟩
    have he : Matrix.of (fun i j => (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l)) = M :=
      Matrix.ext ha
    rw [he]
    exact det_identity_updateRow_ones i₀
  · obtain ⟨a, ha⟩ := exists_hexOddParameters_augmented_face_matrix f hf e ρ
      (1 : Matrix (Fin n) (Fin n) ℝ) (fun i hi => (hnone ⟨i, hi⟩).elim)
    refine ⟨a, ?_⟩
    rw [show Matrix.of (fun i j => (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) from Matrix.ext ha, Matrix.det_one]

noncomputable def hexOddMinorPolynomial {r m n : ℕ} (f : Finset (HexVertex r))
    (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)) : MvPolynomial (HexOddVariable r m) ℝ :=
  (Matrix.of (fun i j => (ρ i).elim 1 (hexOddCoordinatePolynomial (e j).val))).det

theorem eval_hexOddMinorPolynomial {r m n : ℕ} (a : HexOddVariable r m → ℝ)
    (f : Finset (HexVertex r)) (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)) :
    MvPolynomial.eval a (hexOddMinorPolynomial f e ρ) =
      (Matrix.of (fun i j => (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l))).det := by
  rw [hexOddMinorPolynomial, RingHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.eval a ((ρ i).elim 1 (hexOddCoordinatePolynomial (e j).val)) =
    (ρ i).elim 1 (fun l => hexOddConfiguration a (e j).val l)
  cases hi : ρ i with
  | none => simp
  | some l => exact eval_hexOddCoordinatePolynomial a (e j).val l

/-- Oddness does not make any such minor polynomial identically zero. -/
theorem hexOddMinorPolynomial_ne_zero {r m n : ℕ} (f : Finset (HexVertex r))
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (e : Fin n ≃ f)
    (ρ : Fin n ↪ Option (Fin m)) : hexOddMinorPolynomial f e ρ ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_hexOddParameters_augmented_det_one f hf e ρ
  intro h
  have he := eval_hexOddMinorPolynomial a f e ρ
  rw [h, map_zero, ha] at he
  exact zero_ne_one he

/-- Any finite family of actual distinct-row minors can be made nonzero by a
nearby odd perturbation retaining zero-freeness. No polynomial nonvanishing
hypothesis is assumed: it follows from the absence of antipodal vertex pairs. -/
theorem exists_odd_zeroFree_minor_perturbation {r m : ℕ} {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (f : ι → Finset (HexVertex r))
    (hf : ∀ i v, v ∈ f i → hexVertexOpposite v ∉ f i)
    (e : ∀ i, Fin (n i) ≃ f i) (ρ : ∀ i, Fin (n i) ↪ Option (Fin m))
    (p : HexVertex r → Point m) (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hz : HexZeroFree p) (U : Set (HexVertex r → Point m)) (hU : IsOpen U) (hpu : p ∈ U) :
    ∃ a : HexOddVariable r m → ℝ,
      hexOddConfiguration a ∈ U ∧ HexZeroFree (hexOddConfiguration a) ∧
        ∀ i, (Matrix.of (fun j l => (ρ i j).elim 1
          (fun c => hexOddConfiguration a (e i l).val c))).det ≠ 0 := by
  obtain ⟨a, ha, hz', hne⟩ := exists_odd_zeroFree_polynomial_perturbation p hp hz
    (fun i => hexOddMinorPolynomial (f i) (e i) (ρ i))
    (fun i => hexOddMinorPolynomial_ne_zero (f i) (hf i) (e i) (ρ i)) U hU hpu
  exact ⟨a, ha, hz', fun i => by simpa only [eval_hexOddMinorPolynomial] using hne i⟩

end VCDimConvexBound
