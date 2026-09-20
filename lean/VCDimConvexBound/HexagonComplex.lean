import VCDimConvexBound.HexagonGluing
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# The finite complex underlying the normalized hexagon fan

A facet chooses an edge of the six-cycle in every color. Its 2r vertices are
indexed without repetition by `Fin r × Bool`. All nonempty subsets of these
facets form an abstract simplicial complex, the join of r six-cycles.
-/

namespace VCDimConvexBound

/-- The predecessor in cyclic order. -/
def hexPrev (s : Fin 6) : Fin 6 := s + 5

theorem hexNext_ne_self (s : Fin 6) : hexNext s ≠ s := by
  fin_cases s <;> decide

theorem hexPrev_next (s : Fin 6) : hexPrev (hexNext s) = s := by
  fin_cases s <;> decide

theorem hexNext_prev (s : Fin 6) : hexNext (hexPrev s) = s := by
  fin_cases s <;> decide

abbrev HexVertex (r : ℕ) := Fin r × Fin 6

/-- The two endpoints of the chosen edge in each color. -/
def hexFacetVertex {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) : HexVertex r :=
  (e.1, if e.2 then hexNext (s e.1) else s e.1)

theorem hexFacetVertex_injective {r : ℕ} (s : Fin r → Fin 6) :
    Function.Injective (hexFacetVertex s) := by
  rintro ⟨k, b⟩ ⟨l, c⟩ h
  have hkl : k = l := congrArg Prod.fst h
  subst l
  have hbc := congrArg Prod.snd h
  cases b <;> cases c <;> simp [hexFacetVertex] at hbc ⊢
  · exact (hexNext_ne_self (s k) hbc.symm).elim
  · exact (hexNext_ne_self (s k) hbc).elim

/-- The vertex set of a maximal simplex of the join of six-cycles. -/
def hexFacet {r : ℕ} (s : Fin r → Fin 6) : Finset (HexVertex r) :=
  Finset.univ.image (hexFacetVertex s)

theorem mem_hexFacet {r : ℕ} (s : Fin r → Fin 6) (v : HexVertex r) :
    v ∈ hexFacet s ↔ v.2 = s v.1 ∨ v.2 = hexNext (s v.1) := by
  rcases v with ⟨k, j⟩
  constructor
  · intro hv
    obtain ⟨⟨l, b⟩, _, he⟩ := Finset.mem_image.mp hv
    have hl : l = k := congrArg Prod.fst he
    subst l
    have hj := congrArg Prod.snd he
    cases b
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
  · rintro (hj | hj)
    · exact Finset.mem_image.mpr ⟨(k, false), Finset.mem_univ _, Prod.ext rfl hj.symm⟩
    · exact Finset.mem_image.mpr ⟨(k, true), Finset.mem_univ _, Prod.ext rfl hj.symm⟩

theorem card_hexFacet {r : ℕ} (s : Fin r → Fin 6) : (hexFacet s).card = 2 * r := by
  rw [hexFacet, Finset.card_image_of_injective _ (hexFacetVertex_injective s)]
  simp [Nat.mul_comm]

theorem hexFacetVertex_mem {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) :
    hexFacetVertex s e ∈ hexFacet s :=
  Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

/-- The nonempty subsets of the facets form the finite domain complex. -/
def hexFanComplex (r : ℕ) : AbstractSimplicialComplex (HexVertex r) where
  faces := {t | t.Nonempty ∧ ∃ s : Fin r → Fin 6, t ⊆ hexFacet s}
  isRelLowerSet_faces := by
    rintro t ⟨ht, s, hs⟩
    refine ⟨ht, ?_⟩
    intro u hut hu
    exact ⟨hu, s, hut.trans hs⟩
  singleton_mem := by
    intro v
    refine ⟨Finset.singleton_nonempty v, (fun _ => v.2), ?_⟩
    rw [Finset.singleton_subset_iff, mem_hexFacet]
    exact Or.inl rfl

theorem hexFacet_mem_faces {r : ℕ} (hr : 0 < r) (s : Fin r → Fin 6) :
    hexFacet s ∈ (hexFanComplex r).faces := by
  refine ⟨?_, s, Finset.Subset.refl _⟩
  exact ⟨hexFacetVertex s (⟨0, hr⟩, false), hexFacetVertex_mem s _⟩

/-- Every face has at most 2r vertices; facets attain this number. -/
theorem card_le_of_mem_hexFanComplex {r : ℕ} (t : Finset (HexVertex r))
    (ht : t ∈ (hexFanComplex r).faces) : t.card ≤ 2 * r := by
  obtain ⟨_, s, hs⟩ := ht
  exact (Finset.card_le_card hs).trans_eq (card_hexFacet s)

/-- Removing one vertex gives the codimension-one boundary face of a facet. -/
def hexRidge {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) : Finset (HexVertex r) :=
  (hexFacet s).erase (hexFacetVertex s e)

theorem card_hexRidge {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) :
    (hexRidge s e).card + 1 = 2 * r := by
  rw [hexRidge, Finset.card_erase_add_one (hexFacetVertex_mem s e), card_hexFacet]

/-- A ridge retains the other endpoint in the deleted vertex's color. -/
theorem mem_hexRidge {r : ℕ} (s : Fin r → Fin 6) (e : Fin r × Bool) (v : HexVertex r) :
    v ∈ hexRidge s e ↔
      if v.1 = e.1 then v.2 = (if e.2 then s e.1 else hexNext (s e.1))
      else v ∈ hexFacet s := by
  rw [hexRidge, Finset.mem_erase, mem_hexFacet]
  by_cases h : v.1 = e.1
  · rw [if_pos h]
    rcases v with ⟨k, j⟩
    rcases e with ⟨l, b⟩
    dsimp at h
    subst k
    have hn := hexNext_ne_self (s l)
    cases b
    · change ((l, j) ≠ (l, s l) ∧ (j = s l ∨ j = hexNext (s l))) ↔ j = hexNext (s l)
      simp only [ne_eq, Prod.mk.injEq, true_and]
      constructor
      · rintro ⟨hne, he | he⟩
        · exact (hne he).elim
        · exact he
      · intro he
        refine ⟨?_, Or.inr he⟩
        intro ha
        exact hn (he.symm.trans ha)
    · change ((l, j) ≠ (l, hexNext (s l)) ∧ (j = s l ∨ j = hexNext (s l))) ↔ j = s l
      simp only [ne_eq, Prod.mk.injEq, true_and]
      constructor
      · rintro ⟨hne, he | he⟩
        · exact he
        · exact (hne he).elim
      · intro he
        refine ⟨?_, Or.inl he⟩
        intro hb
        exact hn (hb.symm.trans he)
  · rw [if_neg h]
    have hn : v ≠ hexFacetVertex s e := by
      intro he
      exact h (congrArg Prod.fst he)
    simp [hn]

/-- Distinct sector assignments give distinct facets. -/
theorem hexFacet_injective (r : ℕ) : Function.Injective (@hexFacet r) := by
  have hedge : ∀ a b : Fin 6,
      (∀ j, (j = a ∨ j = hexNext a) ↔ (j = b ∨ j = hexNext b)) → a = b := by decide
  intro s t h
  funext k
  apply hedge
  intro j
  rw [← mem_hexFacet s (k, j), h, mem_hexFacet t (k, j)]

/-- Antipodal action on the vertices of the domain complex. -/
def hexVertexOpposite {r : ℕ} (v : HexVertex r) : HexVertex r :=
  (v.1, hexOpposite v.2)

theorem hexVertexOpposite_mem_facet_iff {r : ℕ} (s : Fin r → Fin 6) (v : HexVertex r) :
    hexVertexOpposite v ∈ hexFacet (hexOpposite ∘ s) ↔ v ∈ hexFacet s := by
  simp only [mem_hexFacet, hexVertexOpposite, Function.comp_apply, ← hexOpposite_next]
  rw [hexOpposite_involutive.injective.eq_iff, hexOpposite_involutive.injective.eq_iff]

/-- No simplex contains a vertex together with its antipode. -/
theorem hexVertexOpposite_not_mem_facet {r : ℕ} (s : Fin r → Fin 6) (v : HexVertex r)
    (hv : v ∈ hexFacet s) : hexVertexOpposite v ∉ hexFacet s := by
  have hedge : ∀ a j : Fin 6, (j = a ∨ j = hexNext a) →
      ¬ (hexOpposite j = a ∨ hexOpposite j = hexNext a) := by decide
  exact hedge (s v.1) v.2 ((mem_hexFacet s v).mp hv) ∘ (mem_hexFacet s (hexVertexOpposite v)).mp

end VCDimConvexBound
