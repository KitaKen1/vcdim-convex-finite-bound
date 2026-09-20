import VCDimConvexBound.HexagonOddMinorPolynomials

/-!
# A finite family containing every admissible odd-configuration minor

A square minor has at most m+1 rows: m coordinate rows and one mass row.
Index all such row selections, all vertex sets without antipodal pairs, and
all enumerations of those sets. Thus no choice of face ordering is omitted.
-/

namespace VCDimConvexBound

open scoped Matrix

/-- All square distinct-row minors on vertex sets without antipodal pairs. -/
def HexAllMinorsGeneric {r m : ℕ} (p : HexVertex r → Point m) : Prop :=
  ∀ (n : ℕ) (f : Finset (HexVertex r)),
    (∀ v ∈ f, hexVertexOpposite v ∉ f) →
    ∀ (e : Fin n ≃ f) (ρ : Fin n ↪ Option (Fin m)),
      (Matrix.of (fun i j => (ρ i).elim 1 (fun l => p (e j).val l))).det ≠ 0

/-- The row bound makes the full collection of patterns a finite type. -/
abbrev HexMinorIndex (r m : ℕ) :=
  Σ n : Fin (m + 2),
    Σ f : {f : Finset (HexVertex r) // ∀ v ∈ f, hexVertexOpposite v ∉ f},
      (Fin n.val ≃ f.val) × (Fin n.val ↪ Option (Fin m))

/-- A row embedding has at most m+1 rows, including the optional mass row. -/
theorem hexMinor_row_bound {m n : ℕ} (ρ : Fin n ↪ Option (Fin m)) : n < m + 2 := by
  have h := Fintype.card_le_of_injective ρ ρ.injective
  simp only [Fintype.card_fin, Fintype.card_option] at h
  omega

/-- A nearby odd zero-free configuration satisfies every admissible minor
condition, including every enumeration and every row order. -/
theorem exists_odd_zeroFree_allMinors_perturbation {r m : ℕ}
    (p : HexVertex r → Point m) (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hz : HexZeroFree p) (U : Set (HexVertex r → Point m)) (hU : IsOpen U) (hpu : p ∈ U) :
    ∃ q : HexVertex r → Point m,
      q ∈ U ∧ (∀ v, q (hexVertexOpposite v) = -q v) ∧
        HexZeroFree q ∧ HexAllMinorsGeneric q := by
  classical
  let : Fintype (HexMinorIndex r m) := Fintype.ofFinite _
  obtain ⟨a, ha, hz', hne⟩ := exists_odd_zeroFree_minor_perturbation
    (fun i : HexMinorIndex r m => i.1.val)
    (fun i => i.2.1.val) (fun i => i.2.1.property)
    (fun i => i.2.2.1) (fun i => i.2.2.2) p hp hz U hU hpu
  refine ⟨hexOddConfiguration a, ha, hexOddConfiguration_odd a, hz', ?_⟩
  intro n f hf e ρ
  exact hne ⟨⟨n, hexMinor_row_bound ρ⟩, ⟨f, hf⟩, e, ρ⟩

end VCDimConvexBound
