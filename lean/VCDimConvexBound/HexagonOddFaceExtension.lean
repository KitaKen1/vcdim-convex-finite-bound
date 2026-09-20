import VCDimConvexBound.HexagonOddParameters

/-!
# Prescribing arbitrary images on a face while preserving oddness

A face contains no antipodal pair. Consequently its vertex images are
independent free data inside the space of all odd configurations. This is
the input needed to prove that determinant polynomials are not identically zero.
-/

namespace VCDimConvexBound

theorem hexFace_no_antipodal {r : ℕ} (f : Finset (HexVertex r))
    (hf : f ∈ (hexFanComplex r).faces) :
    ∀ v ∈ f, hexVertexOpposite v ∉ f := by
  obtain ⟨_, s, hs⟩ := hf
  intro v hv hw
  exact hexVertexOpposite_not_mem_facet s v (hs hv) (hs hw)

/-- Extend arbitrary face data to its antipode by negation, and use zero elsewhere. -/
def hexExtendOddFace {r m : ℕ} (f : Finset (HexVertex r)) (b : f → Point m) :
    HexVertex r → Point m := fun v =>
  if h : v ∈ f then b ⟨v, h⟩
  else if hA : hexVertexOpposite v ∈ f then -b ⟨hexVertexOpposite v, hA⟩ else 0

theorem hexExtendOddFace_agrees {r m : ℕ} (f : Finset (HexVertex r)) (b : f → Point m)
    (v : f) : hexExtendOddFace f b v.val = b v := by
  simp [hexExtendOddFace, v.property]

theorem hexExtendOddFace_odd {r m : ℕ} (f : Finset (HexVertex r))
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (b : f → Point m) (v : HexVertex r) :
    hexExtendOddFace f b (hexVertexOpposite v) = -hexExtendOddFace f b v := by
  by_cases hv : v ∈ f
  · have hA := hf v hv
    simp [hexExtendOddFace, hv, hA, hexVertexOpposite_involutive r v]
  · by_cases hA : hexVertexOpposite v ∈ f <;>
      simp [hexExtendOddFace, hv, hA, hexVertexOpposite_involutive r v]

/-- Every prescribed image on a face can be realized by the free odd parameters. -/
theorem exists_hexOddParameters_agree_on_face {r m : ℕ} (f : Finset (HexVertex r))
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (b : f → Point m) :
    ∃ a : HexOddVariable r m → ℝ, ∀ v : f, hexOddConfiguration a v.val = b v := by
  refine ⟨hexOddParameters (hexExtendOddFace f b), ?_⟩
  rw [hexOddConfiguration_parameters _ (hexExtendOddFace_odd f hf b)]
  exact hexExtendOddFace_agrees f b

/-- Arbitrary square coordinate matrices can be prescribed on distinct face vertices. -/
theorem exists_hexOddParameters_face_matrix {r m n : ℕ} (f : Finset (HexVertex r))
    (hf : ∀ v ∈ f, hexVertexOpposite v ∉ f) (e : Fin n ≃ f)
    (ρ : Fin n ↪ Fin m) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ a : HexOddVariable r m → ℝ,
      ∀ i j, hexOddConfiguration a (e j).val (ρ i) = M i j := by
  let b : f → Point m := fun v => Function.extend ρ (fun i => M i (e.symm v)) 0
  obtain ⟨a, ha⟩ := exists_hexOddParameters_agree_on_face f hf b
  refine ⟨a, fun i j => ?_⟩
  rw [ha (e j)]
  simp [b, ρ.injective.extend_apply]

end VCDimConvexBound
