import VCDimConvexBound.CayleyFaces

/-!
# Identification of the colorful complex

Its abstract faces contain at most one point of each color. The Cayley map is
injective under the hypothetical counterexample, and its images are exactly
the faces of the constructed geometric simplicial complex.
-/

namespace VCDimConvexBound

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The join of r discrete m-point sets, described by its nonempty faces. -/
def colorfulComplex (r m : ℕ) : AbstractSimplicialComplex (Fin r × Fin m) where
  faces := {s | s.Nonempty ∧ Set.InjOn Prod.fst (s : Set (Fin r × Fin m))}
  isRelLowerSet_faces := by
    rintro s ⟨hn, hi⟩
    refine ⟨hn, ?_⟩
    intro t hts ht
    exact ⟨ht, hi.mono hts⟩
  singleton_mem := by
    intro e
    refine ⟨Finset.singleton_nonempty e, ?_⟩
    simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst e

/-- A nonempty colorful set extends to a full transversal, including empty color classes. -/
theorem colorful_iff_subset_transversal {r m : ℕ}
    (s : Finset (Fin r × Fin m)) (hs : s.Nonempty) :
    Set.InjOn Prod.fst (s : Set (Fin r × Fin m)) ↔
      ∃ i : Grid r m, ∀ e ∈ s, e.2 = i e.1 := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha⟩ := hs
    let i : Grid r m := fun k => if h : ∃ j, (k, j) ∈ s then h.choose else a.2
    refine ⟨i, fun e he => ?_⟩
    have hex : ∃ j, (e.1, j) ∈ s := ⟨e.2, he⟩
    have hei : (e.1, i e.1) ∈ s := by
      simpa only [i, dif_pos hex] using hex.choose_spec
    exact congrArg Prod.snd (hi he hei rfl)
  · rintro ⟨i, hi⟩ a ha b hb hab
    exact Prod.ext hab (by rw [hi a ha, hi b hb, hab])

/-- Distinct colors have distinct Cayley coordinates. -/
theorem cayleyPoint_color_eq_of_eq {r m D : ℕ}
    (z : Fin r → Fin m → Point D) {a b : Fin r × Fin m}
    (h : cayleyPoint z a = cayleyPoint z b) : a.1 = b.1 := by
  classical
  by_contra hn
  have h' := congrArg (fun x : CayleySpace r D => x.1 a.1) h
  simp [cayleyPoint, hn] at h'

/-- Under a hypothetical counterexample, no vertices are identified by the Cayley realization. -/
theorem cayleyPoint_injective_of_convexIndependent {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    Function.Injective (cayleyPoint z) := by
  intro a b hab
  have hk := cayleyPoint_color_eq_of_eq z hab
  apply Prod.ext hk
  by_contra hj
  let i : Grid r m := fun _ => a.2
  obtain ⟨f, hf⟩ := (convexIndependent_gridSum_iff_commonStrictMaximizers z).mp hz i
  have hlt := hf b.1 b.2 (Ne.symm hj)
  have heq : z a.1 a.2 = z b.1 b.2 := congrArg Prod.snd hab
  dsimp [i] at hlt
  rw [hk] at heq
  rw [← heq] at hlt
  exact lt_irrefl _ hlt

/-- Exactly the abstract colorful faces occur as geometric Cayley faces. -/
theorem mem_cayleyComplex_image_iff {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (s : Finset (Fin r × Fin m)) :
    s.image (cayleyPoint z) ∈ (cayleyComplex z hz).faces ↔
      s ∈ (colorfulComplex r m).faces := by
  classical
  rw [mem_cayleyComplex_faces]
  change (s.image (cayleyPoint z)).Nonempty ∧ _ ↔ s.Nonempty ∧ _
  rw [Finset.image_nonempty]
  apply and_congr_right
  intro hs
  rw [colorful_iff_subset_transversal s hs]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun e he => ?_⟩
    obtain ⟨k, hk⟩ := hi (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    have h := cayleyPoint_injective_of_convexIndependent z hz hk
    rw [← h]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨e.1, ?_⟩
    have h : (e.1, i e.1) = e := Prod.ext rfl (hi e he).symm
    exact congrArg (cayleyPoint z) h

/-- Equality of the abstract face structures, not just a map on individual vertices. -/
theorem cayleyComplex_eq_map_colorful {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    (cayleyComplex z hz).toPreAbstractSimplicialComplex =
      (colorfulComplex r m).toPreAbstractSimplicialComplex.map (cayleyPoint z) := by
  classical
  apply PreAbstractSimplicialComplex.ext
  ext s
  change s ∈ (cayleyComplex z hz).faces ↔
    ∃ t ∈ (colorfulComplex r m).faces, t.image (cayleyPoint z) = s
  constructor
  · intro hs
    obtain ⟨_, i, hi⟩ := (mem_cayleyComplex_faces z hz s).mp hs
    let t : Finset (Fin r × Fin m) := Finset.univ.filter fun e => cayleyPoint z e ∈ s
    have hts : t.image (cayleyPoint z) = s := by
      ext x
      constructor
      · intro hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp he).2
      · intro hx
        obtain ⟨k, hk⟩ := hi hx
        exact Finset.mem_image.mpr ⟨(k, i k), by simp [t, hk, hx], hk⟩
    refine ⟨t, (mem_cayleyComplex_image_iff z hz t).mp ?_, hts⟩
    rwa [hts]
  · rintro ⟨t, ht, rfl⟩
    exact (mem_cayleyComplex_image_iff z hz t).mpr ht

/-- Every Cayley generator is an exposed vertex of the finite hull. -/
theorem cayleyPoint_mem_exposedPoints {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (e : Fin r × Fin m) :
    cayleyPoint z e ∈ (convexHull ℝ (Set.range (cayleyPoint z))).exposedPoints ℝ := by
  rw [mem_exposedPoints_iff_exposed_singleton]
  have h := isExposed_cayley_face z hz (fun _ => e.2) {cayleyPoint z e} (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨e.1, rfl⟩)
  simpa only [convexHull_singleton] using h

/-- The constructed complex has all and only the indexed Cayley points as vertices. -/
theorem cayleyComplex_vertices {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    (cayleyComplex z hz).vertices = Set.range (cayleyPoint z) := by
  classical
  ext x
  rw [Geometry.SimplicialComplex.mem_vertices, mem_cayleyComplex_faces]
  constructor
  · rintro ⟨_, i, hi⟩
    exact subset_cayley_range_of_subset_corner z i _ hi (Finset.mem_singleton_self x)
  · rintro ⟨e, rfl⟩
    refine ⟨Finset.singleton_nonempty _, (fun _ => e.2), ?_⟩
    intro x hx
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    subst x
    exact ⟨e.1, rfl⟩

/-- The expected r*m vertices survive with their original indices. -/
theorem card_cayleyComplex_vertices {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    (cayleyComplex z hz).vertices.ncard = r * m := by
  rw [cayleyComplex_vertices]
  simpa using Set.ncard_range_of_injective (cayleyPoint_injective_of_convexIndependent z hz)

/-- When there are at least two choices per color, every colorful face is proper. -/
theorem cayley_face_ne_whole_hull {r m D : ℕ} (hr : 0 < r) (hm : 2 ≤ m)
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k))) :
    convexHull ℝ S ≠ convexHull ℝ (Set.range (cayleyPoint z)) := by
  classical
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  let k : Fin r := ⟨0, hr⟩
  obtain ⟨j, hj⟩ := exists_ne (i k)
  have hxS : cayleyPoint z (k, j) ∉ S := by
    intro h
    obtain ⟨l, hl⟩ := hS h
    have he := cayleyPoint_injective_of_convexIndependent z hz hl
    have hkl : l = k := congrArg Prod.fst he
    have hji : i l = j := congrArg Prod.snd he
    exact hj (hkl ▸ hji.symm)
  obtain ⟨f, hf, hfS⟩ := exists_cayley_face_support z hz i S hS
  have he := convexHull_eq_zero_face _ S (Set.finite_range _)
    (subset_cayley_range_of_subset_corner z i S hS) f.toLinearMap hf hfS
  intro hwhole
  have hx : cayleyPoint z (k, j) ∈ convexHull ℝ S :=
    hwhole ▸ subset_convexHull ℝ _ (Set.mem_range_self (k, j))
  rw [he] at hx
  exact hxS ((hfS _ (Set.mem_range_self (k, j))).mp hx.2)

end VCDimConvexBound
