import VCDimConvexBound.HexagonAllMinorsGeneric

/-!
# Transport of all minors to the exact coordinate-flag conditions

Rows are represented by distinct optional coordinate indices. The optional
index none is the mass row. The height coordinate is outside the lower
coordinate prefix. These embeddings cover the six determinant patterns in
HexFlagGeneric, including the two successive column deletions.
-/

namespace VCDimConvexBound

open scoped Matrix

/-- Prepend a new value to an embedding of a finite index set. -/
def hexPrependRowEmbedding {α : Type*} {n : ℕ} (ρ : Fin n ↪ α)
    (a : α) (ha : ∀ i, a ≠ ρ i) : Fin (n + 1) ↪ α where
  toFun := Fin.cons a ρ
  inj' := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro h; exact (ha j h).elim
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro h; exact (ha i h.symm).elim
      · intro h
        exact congrArg Fin.succ (ρ.injective h)

/-- The lower coordinate prefix, in the order used by the flag matrices. -/
def hexFlagCoordinateRows {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    Fin k ↪ Option (Fin m) where
  toFun i := some ⟨i.rev.val, lt_of_lt_of_le i.rev.isLt hk⟩
  inj' := by
    intro i j h
    apply Fin.rev_injective
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.val) (Option.some.inj h)

/-- Prepend the constant mass row to the lower coordinate prefix. -/
def hexFlagMassRows {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    Fin (k + 1) ↪ Option (Fin m) :=
  hexPrependRowEmbedding (hexFlagCoordinateRows k hk) none (by
    intro i
    simp [hexFlagCoordinateRows])

/-- Prepend the next height row to the mass row and lower coordinates. -/
def hexFlagAugmentedRows {m : ℕ} (k : ℕ) (hk : k < m) :
    Fin (k + 2) ↪ Option (Fin m) :=
  hexPrependRowEmbedding (hexFlagMassRows k hk.le) (some ⟨k, hk⟩) (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change some (⟨k, hk⟩ : Fin m) ≠ none
      exact Option.some_ne_none _
    · intro h
      have hv : k = j.rev.val := congrArg Fin.val (Option.some.inj h)
      have hj := j.rev.isLt
      omega)

/-- Exclusion of antipodal pairs passes to a subset, including an empty one. -/
theorem hexNoAntipodal_subset {r : ℕ} {f g : Finset (HexVertex r)}
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (hg : g ⊆ f) :
    ∀ v ∈ g, hexVertexOpposite v ∉ g :=
  fun v hv hA => hf v (hg hv) (hg hA)

theorem hexFlagEnumMatrix_eq_coordinate_minor {r m n k : ℕ}
    (p : HexVertex r → Point m) (hk : k ≤ m)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) :
    hexFlagEnumMatrix (hexFlagExtend p) k e =
      Matrix.of (fun i j => (hexFlagCoordinateRows k hk i).elim 1
        (fun l => p (e j).val l)) := by
  ext i j
  have hi : i.rev.val < m := lt_of_lt_of_le i.rev.isLt hk
  change (if h : i.rev.val < m then p (e j).val ⟨i.rev.val, h⟩ else 0) = _
  rw [dif_pos hi]
  rfl

theorem hexFlagMassMatrix_eq_minor {r m n k : ℕ}
    (p : HexVertex r → Point m) (hk : k ≤ m)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) :
    flagPrependRow (fun _ => 1) (hexFlagEnumMatrix (hexFlagExtend p) k e) =
      Matrix.of (fun i j => (hexFlagMassRows k hk i).elim 1
        (fun l => p (e j).val l)) := by
  rw [hexFlagEnumMatrix_eq_coordinate_minor p hk]
  ext i j
  exact Fin.cases rfl (fun _ => rfl) i

theorem hexFlagAugmentedMatrix_eq_minor {r m n k : ℕ}
    (p : HexVertex r → Point m) (hk : k < m)
    {f : Finset (HexVertex r)} (e : Fin n ≃ f) :
    flagPrependRow (fun j => hexFlagExtend p (e j).val k)
      (flagPrependRow (fun _ => 1) (hexFlagEnumMatrix (hexFlagExtend p) k e)) =
      Matrix.of (fun i j => (hexFlagAugmentedRows k hk i).elim 1
        (fun l => p (e j).val l)) := by
  rw [hexFlagMassMatrix_eq_minor p hk.le]
  ext i j
  refine Fin.cases ?_ (fun _ => rfl) i
  change hexFlagExtend p (e j).val k = p (e j).val ⟨k, hk⟩
  simp only [hexFlagExtend, dif_pos hk]

/-- Row prepending commutes with arbitrary column selection. -/
theorem flagPrependRow_submatrix {k n l : ℕ} (z : Fin n → ℝ)
    (X : Matrix (Fin k) (Fin n) ℝ) (c : Fin l → Fin n) :
    (flagPrependRow z X).submatrix id c =
      flagPrependRow (fun j => z (c j)) (X.submatrix id c) := by
  ext i j
  exact Fin.cases rfl (fun _ => rfl) i

/-- Coordinate-only square matrices are among the admissible minors. -/
theorem HexAllMinorsGeneric.coordinate {r m k : ℕ} {p : HexVertex r → Point m}
    (hG : HexAllMinorsGeneric p) (hk : k ≤ m)
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin k ≃ f) : (hexFlagEnumMatrix (hexFlagExtend p) k e).det ≠ 0 := by
  rw [hexFlagEnumMatrix_eq_coordinate_minor p hk]
  exact hG k f hf e (hexFlagCoordinateRows k hk)

/-- Mass-augmented square matrices are among the admissible minors. -/
theorem HexAllMinorsGeneric.mass {r m k : ℕ} {p : HexVertex r → Point m}
    (hG : HexAllMinorsGeneric p) (hk : k ≤ m)
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin (k + 1) ≃ f) :
    (flagPrependRow (fun _ => 1) (hexFlagEnumMatrix (hexFlagExtend p) k e)).det ≠ 0 := by
  rw [hexFlagMassMatrix_eq_minor p hk]
  exact hG (k + 1) f hf e (hexFlagMassRows k hk)

/-- Height-augmented square matrices are the next coordinate prefix. -/
theorem HexAllMinorsGeneric.height {r m k : ℕ} {p : HexVertex r → Point m}
    (hG : HexAllMinorsGeneric p) (hk : k < m)
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin (k + 1) ≃ f) :
    (flagPrependRow (fun j => hexFlagExtend p (e j).val k)
      (hexFlagEnumMatrix (hexFlagExtend p) k e)).det ≠ 0 := by
  rw [← hexFlagEnumMatrix_succ]
  exact hG.coordinate hk f hf e

/-- All four determinant hypotheses of a boundary slice follow from all minors. -/
theorem HexAllMinorsGeneric.slice {r m k : ℕ} {p : HexVertex r → Point m}
    (hG : HexAllMinorsGeneric p) (hk : k < m)
    (f : Finset (HexVertex r)) (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f)
    (e : Fin (k + 2) ≃ f) :
    FlagSliceGeneric (hexFlagEnumMatrix (hexFlagExtend p) k e)
      (fun j => hexFlagExtend p (e j).val k) := by
  have he (i : Fin (k + 2)) := hexNoAntipodal_subset hf (Finset.erase_subset (e i).val f)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [sliceDeleteColumn, flagConstraintMatrix, flagPrependRow_submatrix]
    exact hG.mass hk.le _ (he i) (hexFaceEraseEnumeration e i)
  · intro i j
    exact hG.coordinate hk.le _
      (hexNoAntipodal_subset (he i) (Finset.erase_subset _ _))
      (hexFaceEraseEnumeration (hexFaceEraseEnumeration e i) j)
  · rw [flagConstraintMatrix, hexFlagAugmentedMatrix_eq_minor p hk]
    exact hG (k + 2) f hf e (hexFlagAugmentedRows k hk)
  · intro i
    rw [sliceDeleteColumn, flagPrependRow_submatrix]
    exact hG.height hk _ (he i) (hexFaceEraseEnumeration e i)

/-- The full finite minor family supplies exactly the existing flag structure. -/
theorem HexAllMinorsGeneric.flag {r : ℕ} {p : HexVertex r → Point (2 * r - 1)}
    (hG : HexAllMinorsGeneric p) : HexFlagGeneric (hexFlagExtend p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk f hf e
    exact hG.slice (by omega) f (hexFace_no_antipodal f hf) e
  · intro k hk f hf e
    exact hG.mass (by omega) f (hexFace_no_antipodal f hf) e
  · intro k hk f hf e
    exact hG.height (by omega) f (hexFace_no_antipodal f hf) e

end VCDimConvexBound
