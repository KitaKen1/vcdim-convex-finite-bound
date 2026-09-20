import VCDimConvexBound.HexagonModTwo

/-!
# Add a color to mod-two chains

A finite set of new hexagon vertices is joined with an old face whose colors
are shifted by one. The two vertex sets are disjoint. The actual deletion
boundary satisfies the mod-two join formula, including empty faces.
-/

namespace VCDimConvexBound

open scoped BigOperators

def hexHeadVertex {r : ℕ} (j : Fin 6) : HexVertex (r + 1) := (0, j)
def hexTailVertex {r : ℕ} (v : HexVertex r) : HexVertex (r + 1) := (v.1.succ, v.2)

theorem hexHeadVertex_injective (r : ℕ) : Function.Injective (@hexHeadVertex r) := by
  intro a b h
  exact congrArg Prod.snd h

theorem hexTailVertex_injective (r : ℕ) : Function.Injective (@hexTailVertex r) := by
  intro a b h
  have h₁ : a.1.succ = b.1.succ := congrArg Prod.fst h
  have h₂ : a.2 = b.2 := congrArg (fun v : HexVertex (r + 1) => v.2) h
  exact Prod.ext (Fin.succ_injective _ h₁) h₂

def hexJoinFace {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    Finset (HexVertex (r + 1)) := a.image hexHeadVertex ∪ t.image hexTailVertex

theorem hexJoinFace_head_mem {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r))
    (j : Fin 6) : hexHeadVertex j ∈ hexJoinFace a t ↔ j ∈ a := by
  simp [hexJoinFace, hexHeadVertex, hexTailVertex]

theorem hexJoinFace_tail_mem {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r))
    (v : HexVertex r) : hexTailVertex v ∈ hexJoinFace a t ↔ v ∈ t := by
  simp [hexJoinFace, hexHeadVertex, hexTailVertex, Prod.mk.injEq, Ne.symm (Fin.succ_ne_zero _)]

theorem hexJoinFace_disjoint {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    Disjoint (a.image (@hexHeadVertex r)) (t.image hexTailVertex) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨w, _, he⟩ := Finset.mem_image.mp hw
  have h := congrArg Prod.fst he
  simp [hexHeadVertex, hexTailVertex] at h

theorem hexJoinFace_erase_head {r : ℕ} (a : Finset (Fin 6))
    (t : Finset (HexVertex r)) (j : Fin 6) :
    (hexJoinFace a t).erase (hexHeadVertex j) = hexJoinFace (a.erase j) t := by
  ext v
  rcases v with ⟨k, l⟩
  refine Fin.cases ?_ (fun k => ?_) k
  · change hexHeadVertex l ∈ _ ↔ hexHeadVertex l ∈ _
    simp only [Finset.mem_erase, hexJoinFace_head_mem]
    simp [hexHeadVertex]
  · change hexTailVertex (k, l) ∈ _ ↔ hexTailVertex (k, l) ∈ _
    simp only [Finset.mem_erase, hexJoinFace_tail_mem]
    simp [hexTailVertex, hexHeadVertex]

theorem hexJoinFace_erase_tail {r : ℕ} (a : Finset (Fin 6))
    (t : Finset (HexVertex r)) (w : HexVertex r) :
    (hexJoinFace a t).erase (hexTailVertex w) = hexJoinFace a (t.erase w) := by
  ext v
  rcases v with ⟨k, l⟩
  refine Fin.cases ?_ (fun k => ?_) k
  · change hexHeadVertex l ∈ _ ↔ hexHeadVertex l ∈ _
    simp only [Finset.mem_erase, hexJoinFace_head_mem]
    simp [hexHeadVertex, hexTailVertex, Ne.symm (Fin.succ_ne_zero _)]
  · change hexTailVertex (k, l) ∈ _ ↔ hexTailVertex (k, l) ∈ _
    simp [Finset.mem_erase, hexJoinFace_tail_mem, (hexTailVertex_injective r).ne_iff]

/-- The join formula on the basis chain of any old face. -/
theorem hexChainBoundary_join_basis {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    hexChainBoundary (r + 1) (hexFaceBasis (hexJoinFace a t)) =
      (∑ j ∈ a, hexFaceBasis (hexJoinFace (a.erase j) t)) +
        ∑ v ∈ t, hexFaceBasis (hexJoinFace a (t.erase v)) := by
  rw [hexChainBoundary_basis]
  change (∑ v ∈ a.image hexHeadVertex ∪ t.image hexTailVertex,
    hexFaceBasis ((hexJoinFace a t).erase v)) = _
  rw [Finset.sum_union (hexJoinFace_disjoint a t)]
  rw [Finset.sum_image (fun i _ j _ h => hexHeadVertex_injective r h),
    Finset.sum_image (fun i _ j _ h => hexTailVertex_injective r h)]
  simp_rw [hexJoinFace_erase_head, hexJoinFace_erase_tail]

/-- Every finite chain is the sum of its basis coefficients. -/
theorem sum_smul_hexFaceBasis {r : ℕ} (c : HexModTwoChain r) :
    (∑ t : Finset (HexVertex r), c t • hexFaceBasis t) = c := by
  funext f
  simp [Finset.sum_apply, Pi.smul_apply, hexFaceBasis, smul_eq_mul]

/-- Equality of linear chain operators can be checked on the face basis. -/
theorem hexChainMap_ext {r p : ℕ}
    (f g : HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain p)
    (h : ∀ t, f (hexFaceBasis t) = g (hexFaceBasis t)) : f = g := by
  apply LinearMap.ext
  intro c
  rw [← sum_smul_hexFaceBasis c]
  simp only [map_sum, map_smul, h]

/-- Join a fixed new-color face with an arbitrary old chain. -/
noncomputable def hexPrependChain {r : ℕ} (a : Finset (Fin 6)) :
    HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain (r + 1) where
  toFun c := ∑ t : Finset (HexVertex r), c t • hexFaceBasis (hexJoinFace a t)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' x c := by simp [smul_smul, Finset.smul_sum]

theorem hexPrependChain_basis {r : ℕ} (a : Finset (Fin 6)) (t : Finset (HexVertex r)) :
    hexPrependChain a (hexFaceBasis t) = hexFaceBasis (hexJoinFace a t) := by
  simp [hexPrependChain, hexFaceBasis]

/-- The mod-two Leibniz rule as an equality of actual boundary operators. -/
theorem hexChainBoundary_prepend_eq {r : ℕ} (a : Finset (Fin 6)) :
    (hexChainBoundary (r + 1)).comp (hexPrependChain a) =
      (∑ j ∈ a, hexPrependChain (a.erase j)) +
        (hexPrependChain a).comp (hexChainBoundary r) := by
  apply hexChainMap_ext
  intro t
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
    hexPrependChain_basis, hexChainBoundary_basis, map_sum]
  simpa only [hexChainBoundary_basis] using hexChainBoundary_join_basis a t

theorem hexChainBoundary_prepend {r : ℕ} (a : Finset (Fin 6)) (c : HexModTwoChain r) :
    hexChainBoundary (r + 1) (hexPrependChain a c) =
      (∑ j ∈ a, hexPrependChain (a.erase j) c) +
        hexPrependChain a (hexChainBoundary r c) := by
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply] using
    congrArg (fun f : HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain (r + 1) => f c)
      (hexChainBoundary_prepend_eq a)

end VCDimConvexBound
