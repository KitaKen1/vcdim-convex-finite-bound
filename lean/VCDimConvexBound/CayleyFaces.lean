import VCDimConvexBound.CayleyDimension
import VCDimConvexBound.FiniteExposedFaces
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!
# A direct Cayley realization of the colorful faces

For the standard product needed by the VC argument, append the color basis
vector to each input point. Common strict support then exposes every subset
of a transversal. These simplices meet exactly along their common vertices,
so they form a geometric simplicial complex in mathlib. No general Gale
polytope duality or non-embedding theorem is used.
-/

namespace VCDimConvexBound

open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev CayleySpace (r D : ℕ) := (Fin r → ℝ) × Point D

/-- A point together with its color coordinate. -/
def cayleyPoint {r m D : ℕ} (z : Fin r → Fin m → Point D) (e : Fin r × Fin m) :
    CayleySpace r D := (Pi.single e.1 1, z e.1 e.2)

/-- Transversals are independent already in the color coordinates. -/
theorem linearIndependent_cayleyCorner {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) :
    LinearIndependent ℝ (fun k => cayleyPoint z (k, i k)) := by
  apply LinearIndependent.of_comp (LinearMap.fst ℝ (Fin r → ℝ) (Point D))
  exact Pi.linearIndependent_single_one (Fin r) ℝ

theorem affineIndependent_cayleyCorner {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) :
    AffineIndependent ℝ (fun k => cayleyPoint z (k, i k)) :=
  (linearIndependent_cayleyCorner z i).affineIndependent

/-- Penalize the omitted colors as well as the unselected points. -/
noncomputable def cayleySupport {r m D : ℕ} (z : Fin r → Fin m → Point D)
    (i : Grid r m) (S : Set (CayleySpace r D)) (f : Point D →L[ℝ] ℝ) :
    CayleySpace r D →L[ℝ] ℝ := by
  classical
  let c : Fin r → ℝ := fun k => f (z k (i k)) +
    if cayleyPoint z (k, i k) ∈ S then 0 else 1
  exact LinearMap.toContinuousLinearMap {
    toFun := fun x => f x.2 - ∑ k, x.1 k * c k
    map_add' := by
      intro x y
      simp only [Prod.snd_add, map_add, Prod.fst_add, Pi.add_apply,
        add_mul, Finset.sum_add_distrib]
      ring
    map_smul' := by
      intro a x
      change f (a • x.2) - ∑ k, (a * x.1 k) * c k =
        a * (f x.2 - ∑ k, x.1 k * c k)
      simp only [map_smul, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_sub] }

@[simp] theorem cayleySupport_apply_point {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (S : Set (CayleySpace r D))
    (f : Point D →L[ℝ] ℝ) (e : Fin r × Fin m) :
    cayleySupport z i S f (cayleyPoint z e) = f (z e.1 e.2) -
      (f (z e.1 (i e.1)) + if cayleyPoint z (e.1, i e.1) ∈ S then 0 else 1) := by
  classical
  simp [cayleySupport, cayleyPoint, Pi.single_apply]

/-- The exposing functional is nonpositive on every Cayley generator. -/
theorem cayleySupport_nonpos {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (S : Set (CayleySpace r D))
    (f : Point D →L[ℝ] ℝ)
    (hf : ∀ k j, j ≠ i k → f (z k j) < f (z k (i k))) (e : Fin r × Fin m) :
    cayleySupport z i S f (cayleyPoint z e) ≤ 0 := by
  classical
  have hle : f (z e.1 e.2) ≤ f (z e.1 (i e.1)) := by
    by_cases h : e.2 = i e.1
    · rw [h]
    · exact (hf _ _ h).le
  rw [cayleySupport_apply_point]
  split_ifs <;> linarith

/-- Exactly the prescribed transversal subset lies on the supporting hyperplane. -/
theorem cayleySupport_eq_zero_iff {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k)))
    (f : Point D →L[ℝ] ℝ)
    (hf : ∀ k j, j ≠ i k → f (z k j) < f (z k (i k))) (e : Fin r × Fin m) :
    cayleySupport z i S f (cayleyPoint z e) = 0 ↔ cayleyPoint z e ∈ S := by
  classical
  rcases e with ⟨k, j⟩
  constructor
  · intro hzero
    have hj : j = i k := by
      by_contra hj
      have hlt := hf k j hj
      rw [cayleySupport_apply_point] at hzero
      split_ifs at hzero <;> linarith
    subst j
    by_contra hs
    simp [hs] at hzero
  · intro hs
    obtain ⟨l, hl⟩ := hS hs
    rw [← hl] at hs ⊢
    simp [hs]

/-- Every subset of a transversal admits an exact global exposing functional. -/
theorem exists_cayley_face_support {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k))) :
    ∃ g : CayleySpace r D →L[ℝ] ℝ,
      (∀ x ∈ Set.range (cayleyPoint z), g x ≤ 0) ∧
      (∀ x ∈ Set.range (cayleyPoint z), g x = 0 ↔ x ∈ S) := by
  obtain ⟨f, hf⟩ := (convexIndependent_gridSum_iff_commonStrictMaximizers z).mp hz i
  refine ⟨cayleySupport z i S f, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩
    exact cayleySupport_nonpos z i S f hf e
  · rintro _ ⟨e, rfl⟩
    exact cayleySupport_eq_zero_iff z i S hS f hf e

/-- A transversal subset uses only generators of the Cayley polytope. -/
theorem subset_cayley_range_of_subset_corner {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k))) :
    S ⊆ Set.range (cayleyPoint z) := by
  intro x hx
  obtain ⟨k, rfl⟩ := hS hx
  exact Set.mem_range_self (k, i k)

/-- The colorful simplices are genuine exposed faces of the finite Cayley hull. -/
theorem isExposed_cayley_face {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i : Grid r m) (S : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k))) :
    IsExposed ℝ (convexHull ℝ (Set.range (cayleyPoint z))) (convexHull ℝ S) := by
  obtain ⟨f, hf, hfS⟩ := exists_cayley_face_support z hz i S hS
  exact isExposed_convexHull_of_zero_face _ S (Set.finite_range _)
    (subset_cayley_range_of_subset_corner z i S hS) f hf hfS

/-- Colorful faces intersect in precisely the convex hull of their common vertices. -/
theorem cayley_faces_inter {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (i j : Grid r m) (S T : Set (CayleySpace r D))
    (hS : S ⊆ Set.range (fun k => cayleyPoint z (k, i k)))
    (hT : T ⊆ Set.range (fun k => cayleyPoint z (k, j k))) :
    convexHull ℝ S ∩ convexHull ℝ T = convexHull ℝ (S ∩ T) := by
  obtain ⟨f, hf, hfS⟩ := exists_cayley_face_support z hz i S hS
  exact convexHull_inter_convexHull_of_zero_face _ S T (Set.finite_range _)
    (subset_cayley_range_of_subset_corner z i S hS)
    (subset_cayley_range_of_subset_corner z j T hT) f.toLinearMap hf hfS

/-- The family of nonempty colorful simplices, with the geometric gluing proof included. -/
noncomputable def cayleyComplex {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z)) :
    Geometry.SimplicialComplex ℝ (CayleySpace r D) := by
  classical
  apply Geometry.SimplicialComplex.ofErase
    {s | ∃ i : Grid r m, (s : Set (CayleySpace r D)) ⊆
      Set.range (fun k => cayleyPoint z (k, i k))}
  · rintro s ⟨i, hs⟩
    exact (affineIndependent_cayleyCorner z i).range.mono hs
  · intro s t hts hs
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, fun x hx => hi (hts hx)⟩
  · rintro s ⟨i, hs⟩ t ⟨j, ht⟩
    exact (cayley_faces_inter z hz i j _ _ hs ht).le

/-- The constructed complex has exactly the nonempty subsets of transversals as faces. -/
theorem mem_cayleyComplex_faces {r m D : ℕ}
    (z : Fin r → Fin m → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (s : Finset (CayleySpace r D)) :
    s ∈ (cayleyComplex z hz).faces ↔ s.Nonempty ∧
      ∃ i : Grid r m, (s : Set (CayleySpace r D)) ⊆
        Set.range (fun k => cayleyPoint z (k, i k)) := by
  classical
  change ((∃ i : Grid r m, (s : Set (CayleySpace r D)) ⊆
    Set.range (fun k => cayleyPoint z (k, i k))) ∧ s ∉ ({∅} : Set _)) ↔ _
  simp only [Set.mem_singleton_iff, Finset.nonempty_iff_ne_empty, and_comm]

end VCDimConvexBound
