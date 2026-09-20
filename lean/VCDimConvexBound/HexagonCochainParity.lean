import VCDimConvexBound.HexagonHemisphereTower

/-!
# Pairing face cochains with the hemisphere tower

This file proves parity propagation from two explicit identities on actual
faces. It does not assert that geometric crossing indicators satisfy those
identities: transporting the matrix lemmas remains a separate obligation.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Evaluate a face cochain on a finite mod-two chain. -/
noncomputable def hexCochainEval {r : ℕ} (q : HexModTwoChain r) :
    HexModTwoChain r →ₗ[ZMod 2] ZMod 2 where
  toFun c := ∑ f : Finset (HexVertex r), c f * q f
  map_add' c d := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [smul_eq_mul, Finset.mul_sum, mul_assoc]

def hexCoboundary {r : ℕ} (a : HexModTwoChain r) : HexModTwoChain r :=
  fun f => ∑ v ∈ f, a (f.erase v)

def hexAntipodalCochain {r : ℕ} (a : HexModTwoChain r) : HexModTwoChain r :=
  fun f => a (f.image hexVertexOpposite)

theorem hexCochainEval_basis {r : ℕ} (q : HexModTwoChain r) (f : Finset (HexVertex r)) :
    hexCochainEval q (hexFaceBasis f) = q f := by
  simp [hexCochainEval, hexFaceBasis]

theorem hexCochainEval_add {r : ℕ} (q a c : HexModTwoChain r) :
    hexCochainEval (q + a) c = hexCochainEval q c + hexCochainEval a c := by
  simp [hexCochainEval, mul_add, Finset.sum_add_distrib]

/-- Discrete Stokes formula for the actual vertex-deletion boundary. -/
theorem hexCochainEval_coboundary {r : ℕ} (a c : HexModTwoChain r) :
    hexCochainEval (hexCoboundary a) c = hexCochainEval a (hexChainBoundary r c) := by
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexChainBoundary_basis, hexCochainEval_basis, hexCoboundary]

theorem hexCochainEval_antipodal {r : ℕ} (a c : HexModTwoChain r) :
    hexCochainEval (hexAntipodalCochain a) c =
      hexCochainEval a (hexAntipodalChain r c) := by
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, hexAntipodalChain_basis, hexCochainEval_basis,
    hexAntipodalCochain]

/-- Cochain equality is needed only on the dimension and complex supporting c. -/
theorem hexCochainEval_congr_onFaces {r h : ℕ} {c : HexModTwoChain r}
    (hc : HexChainOnFaces h c) (hh : 0 < h) (q a : HexModTwoChain r)
    (he : ∀ f ∈ (hexFanComplex r).faces, f.card = h → q f = a f) :
    hexCochainEval q c = hexCochainEval a c := by
  change (∑ f, c f * q f) = ∑ f, c f * a f
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : c f = 0
  · simp [hf]
  · rw [he f (hc.mem_faces hh hf) (hc f hf).1]

/-- A nonzero evaluation has a face contributing to it. -/
theorem hexCochainEval_exists {r : ℕ} {q c : HexModTwoChain r}
    (h : hexCochainEval q c ≠ 0) :
    ∃ f, c f ≠ 0 ∧ q f ≠ 0 := by
  obtain ⟨f, _, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨f, left_ne_zero_of_mul hf, right_ne_zero_of_mul hf⟩

/-- One step of parity propagation, assuming the two identities on actual faces. -/
theorem hexHemisphereTower_parity_step {r k : ℕ} (hk : k + 1 < 2 * r)
    (qNext q a : HexModTwoChain r)
    (hboundary : ∀ f ∈ (hexFanComplex r).faces, f.card = k + 2 →
      qNext f = hexCoboundary a f)
    (hantipodal : ∀ f ∈ (hexFanComplex r).faces, f.card = k + 1 →
      q f = a f + hexAntipodalCochain a f) :
    hexCochainEval qNext (hexHemisphereTower r (k + 1)) =
      hexCochainEval q (hexHemisphereTower r k) := by
  calc
    _ = hexCochainEval (hexCoboundary a) (hexHemisphereTower r (k + 1)) :=
      hexCochainEval_congr_onFaces (hexHemisphereTower_onFaces hk) (by omega)
        _ _ hboundary
    _ = hexCochainEval a (hexChainBoundary r (hexHemisphereTower r (k + 1))) :=
      hexCochainEval_coboundary _ _
    _ = hexCochainEval a (hexHemisphereTower r k) +
        hexCochainEval a (hexAntipodalChain r (hexHemisphereTower r k)) := by
      rw [hexHemisphereTower_boundary hk, map_add]
    _ = hexCochainEval (a + hexAntipodalCochain a) (hexHemisphereTower r k) := by
      rw [hexCochainEval_add, hexCochainEval_antipodal]
    _ = hexCochainEval q (hexHemisphereTower r k) :=
      (hexCochainEval_congr_onFaces (hexHemisphereTower_onFaces (by omega))
        (by omega) _ _ hantipodal).symm

/-- All tower evaluations are one, conditional on the face-level flag identities. -/
theorem hexHemisphereTower_parity_one {r : ℕ}
    (q a : ℕ → HexModTwoChain r)
    (hbase : ∀ v : HexVertex r, q 0 {v} = 1)
    (hboundary : ∀ k, k + 1 < 2 * r →
      ∀ f ∈ (hexFanComplex r).faces, f.card = k + 2 →
        q (k + 1) f = hexCoboundary (a k) f)
    (hantipodal : ∀ k, k + 1 < 2 * r →
      ∀ f ∈ (hexFanComplex r).faces, f.card = k + 1 →
        q k f = a k f + hexAntipodalCochain (a k) f)
    {k : ℕ} (hk : k < 2 * r) :
    hexCochainEval (q k) (hexHemisphereTower r k) = 1 := by
  induction k with
  | zero =>
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    rw [hexHemisphereTower_base, hexCochainEval_basis]
    exact hbase _
  | succ k ih =>
    rw [hexHemisphereTower_parity_step hk (q (k + 1)) (q k) (a k)
      (hboundary k hk) (hantipodal k hk)]
    exact ih (by omega)

/-- The face-level identities force a top-dimensional facet with nonzero q. -/
theorem hexHemisphereTower_exists_top_crossing {r : ℕ} (hr : 0 < r)
    (q a : ℕ → HexModTwoChain r)
    (hbase : ∀ v : HexVertex r, q 0 {v} = 1)
    (hboundary : ∀ k, k + 1 < 2 * r →
      ∀ f ∈ (hexFanComplex r).faces, f.card = k + 2 →
        q (k + 1) f = hexCoboundary (a k) f)
    (hantipodal : ∀ k, k + 1 < 2 * r →
      ∀ f ∈ (hexFanComplex r).faces, f.card = k + 1 →
        q k f = a k f + hexAntipodalCochain (a k) f) :
    ∃ s : Fin r → Fin 6, q (2 * r - 1) (hexFacet s) ≠ 0 := by
  have hk : 2 * r - 1 < 2 * r := by omega
  have h := hexHemisphereTower_parity_one q a hbase hboundary hantipodal hk
  obtain ⟨f, hf, hq⟩ := hexCochainEval_exists (show
    hexCochainEval (q (2 * r - 1)) (hexHemisphereTower r (2 * r - 1)) ≠ 0 by
      rw [h]; exact one_ne_zero)
  obtain ⟨hcard, s, hs⟩ := hexHemisphereTower_onFaces hk f hf
  have he : f = hexFacet s := Finset.eq_of_subset_of_card_le hs (by
    rw [card_hexFacet, hcard]; omega)
  exact ⟨s, he ▸ hq⟩

end VCDimConvexBound
