import VCDimConvexBound.HexagonAntipodalChains

/-!
# Dimensions and face support of hexagon chains

The empty face is allowed here, as required by the augmented boundary.
Positive cardinality will recover membership in the actual simplicial complex.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- Every nonzero coefficient is an h-vertex subface of a hexagon facet. -/
def HexChainOnFaces {r : ℕ} (h : ℕ) (c : HexModTwoChain r) : Prop :=
  ∀ t, c t ≠ 0 → t.card = h ∧ ∃ s : Fin r → Fin 6, t ⊆ hexFacet s

theorem hexJoinFace_card {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    (hexJoinFace a t).card = a.card + t.card := by
  rw [hexJoinFace, Finset.card_union_of_disjoint (hexJoinFace_disjoint a t),
    Finset.card_image_of_injective _ (hexHeadVertex_injective r),
    Finset.card_image_of_injective _ (hexTailVertex_injective r)]

theorem hexJoinFace_subset_facet {r : ℕ} {a : Finset (Fin 6)}
    {t : Finset (HexVertex r)} {j : Fin 6} {s : Fin r → Fin 6}
    (ha : a ⊆ {j, hexNext j}) (ht : t ⊆ hexFacet s) :
    hexJoinFace a t ⊆ hexFacet (Fin.cons j s) := by
  rw [hexFacet_cons]
  exact Finset.union_subset_union (Finset.image_subset_image ha) (Finset.image_subset_image ht)

theorem HexChainOnFaces.basis {r h : ℕ} (t : Finset (HexVertex r))
    (ht : t.card = h) (hs : ∃ s : Fin r → Fin 6, t ⊆ hexFacet s) :
    HexChainOnFaces h (hexFaceBasis t) := by
  intro f hf
  have he : t = f := by
    by_contra he
    exact hf (by simp [hexFaceBasis, he])
  subst f
  exact ⟨ht, hs⟩

theorem HexChainOnFaces.sum {r h : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → HexModTwoChain r) (hc : ∀ i ∈ s, HexChainOnFaces h (c i)) :
    HexChainOnFaces h (∑ i ∈ s, c i) := by
  intro t ht
  by_contra hn
  apply ht
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hci
  exact hn (hc i hi t hci)

theorem HexChainOnFaces.prepend {r h : ℕ} {c : HexModTwoChain r}
    (hc : HexChainOnFaces h c) (a : Finset (Fin 6))
    (ha : ∃ j : Fin 6, a ⊆ {j, hexNext j}) :
    HexChainOnFaces (a.card + h) (hexPrependChain a c) := by
  intro f hf
  by_contra hn
  apply hf
  change (∑ t : Finset (HexVertex r), c t • hexFaceBasis (hexJoinFace a t)) f = 0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro t _
  by_cases hct : c t = 0
  · simp [hct]
  by_cases he : hexJoinFace a t = f
  · obtain ⟨ht, s, hs⟩ := hc t hct
    obtain ⟨j, hj⟩ := ha
    exact (hn ⟨he ▸ (hexJoinFace_card a t).trans (congrArg (a.card + ·) ht),
      ⟨Fin.cons j s, he ▸ hexJoinFace_subset_facet hj hs⟩⟩).elim
  · simp [hexFaceBasis, he]

theorem hexFundamentalChain_onFaces (r : ℕ) :
    HexChainOnFaces (2 * r) (hexFundamentalChain r) := by
  apply HexChainOnFaces.sum
  intro s _
  exact HexChainOnFaces.basis _ (card_hexFacet s) ⟨s, Finset.Subset.refl _⟩

theorem hexConeChain_onFaces (r : ℕ) (j : Fin 6) :
    HexChainOnFaces (2 * r + 1) (hexConeChain r j) := by
  have h := (hexFundamentalChain_onFaces r).prepend {j}
    ⟨j, by simp⟩
  simpa [hexConeChain, Nat.add_comm] using h

theorem hexHemisphereChain_onFaces (r : ℕ) :
    HexChainOnFaces (2 * r + 2) (hexHemisphereChain r) := by
  apply HexChainOnFaces.sum
  intro j _
  have h := (hexFundamentalChain_onFaces r).prepend {j, hexNext j}
    ⟨j, Finset.Subset.refl _⟩
  simpa [Finset.card_insert_of_notMem, Ne.symm (hexNext_ne_self j), Nat.add_comm] using h

theorem HexChainOnFaces.mem_faces {r h : ℕ} {c : HexModTwoChain r}
    (hc : HexChainOnFaces h c) (hh : 0 < h) {t : Finset (HexVertex r)} (ht : c t ≠ 0) :
    t ∈ (hexFanComplex r).faces := by
  obtain ⟨hcard, hs⟩ := hc t ht
  exact ⟨Finset.card_pos.mp (hcard ▸ hh), hs⟩

end VCDimConvexBound
