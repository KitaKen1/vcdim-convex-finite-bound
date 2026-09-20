import VCDimConvexBound.HexagonFan
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear pieces and normalized kernel certificates

The actual hexagon map agrees with one of 6^r linear maps on each closed
product sector. A non-origin zero is equivalent to a nonnegative kernel
vector of total coordinate mass one in one of these finitely many pieces.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- The linear extension of a fixed piece to all sector coordinates. -/
noncomputable def hexPieceLinear {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) : HexagonDomain r →ₗ[ℝ] CayleySpace r D where
  toFun t := ∑ e : Fin r × Fin 3, hexSectorWeight (s e.1) (t e.1) e.2 •
    (cayleyPoint z e - finiteAverage (cayleyPoint z))
  map_add' t u := by simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [map_smul, mul_smul, Finset.smul_sum]

/-- Each linear piece is the original map on its closed product sector. -/
theorem hexagonCayleyMap_sector {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (s : Fin r → Fin 6) (t : HexagonDomain r) (ht : HexNonnegative t) :
    hexagonCayleyMap z (hexSectorArray s t) = hexPieceLinear z s t := by
  change (∑ e, hexWeight (hexSectorMap (s e.1) (t e.1)) e.2 •
    (cayleyPoint z e - finiteAverage (cayleyPoint z))) -
    (∑ e, hexWeight (-hexSectorMap (s e.1) (t e.1)) e.2 •
    (cayleyPoint z e - finiteAverage (cayleyPoint z))) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← sub_smul, hexWeight_sub_eq_sector _ _ (ht e.1).1 (ht e.1).2]

/-- A piece lands in the color-sum kernel even outside its defining nonnegative sector. -/
theorem hexPieceLinear_mem_ker {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (s : Fin r → Fin 6) (t : HexagonDomain r) :
    hexPieceLinear z s t ∈ LinearMap.ker (cayleyColorSum r D) := by
  rw [LinearMap.mem_ker]
  exact cayleyColorSum_centeredCombination hr (by decide) z
    (fun e => hexSectorWeight (s e.1) (t e.1) e.2)

/-- Regard a piece as a linear map into the correct lower-dimensional space. -/
noncomputable def hexPieceKernelLinear {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (s : Fin r → Fin 6) :
    HexagonDomain r →ₗ[ℝ] LinearMap.ker (cayleyColorSum r D) :=
  LinearMap.codRestrict _ (hexPieceLinear z s) (hexPieceLinear_mem_ker hr z s)

/-- Rank-nullity supplies a nonzero kernel vector in every piece.
This does not say that the vector belongs to the nonnegative sector. -/
theorem exists_ne_zero_hexPiece_kernel (D : ℕ) (hD : 0 < D)
    (z : Fin D → Fin 3 → Point D) (s : Fin D → Fin 6) :
    ∃ t : HexagonDomain D, t ≠ 0 ∧ hexPieceLinear z s t = 0 := by
  have hdim : Module.finrank ℝ (LinearMap.ker (cayleyColorSum D D)) <
      Module.finrank ℝ (HexagonDomain D) := by
    rw [finrank_ker_cayleyColorSum D hD, finrank_hexagonDomain]
    omega
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := hexPieceKernelLinear hD z s) hdim
  obtain ⟨t, ht, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨t, hn, congrArg Subtype.val (LinearMap.mem_ker.mp ht)⟩

/-- The mass used to normalize nonnegative sector coordinates. -/
def hexParameterMass {r : ℕ} : HexagonDomain r →ₗ[ℝ] ℝ where
  toFun t := ∑ k, ((t k).1 + (t k).2)
  map_add' t u := by
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  map_smul' a t := by
    simp [smul_eq_mul, mul_add, Finset.mul_sum]

/-- Nonnegative coordinates have positive mass unless all coordinates vanish. -/
theorem hexParameterMass_pos {r : ℕ} (t : HexagonDomain r)
    (ht : HexNonnegative t) (hn : t ≠ 0) : 0 < hexParameterMass t := by
  have hnonneg : ∀ k, 0 ≤ (t k).1 + (t k).2 := fun k => add_nonneg (ht k).1 (ht k).2
  have hs : 0 ≤ hexParameterMass t := by
    change 0 ≤ ∑ k, ((t k).1 + (t k).2)
    exact Finset.sum_nonneg (fun k _ => hnonneg k)
  by_contra h
  have heq : hexParameterMass t = 0 := le_antisymm (le_of_not_gt h) hs
  change (∑ k, ((t k).1 + (t k).2)) = 0 at heq
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg k)).mp heq
  apply hn
  funext k
  have h₀ := hk k (Finset.mem_univ k)
  have h₁ := (ht k).1
  have h₂ := (ht k).2
  apply Prod.ext <;> change _ = 0 <;> linarith

theorem HexNonnegative.smul {r : ℕ} {t : HexagonDomain r} (ht : HexNonnegative t)
    {a : ℝ} (ha : 0 ≤ a) : HexNonnegative (a • t) := by
  intro k
  exact ⟨mul_nonneg ha (ht k).1, mul_nonneg ha (ht k).2⟩

/-- A zero of the nonlinear formula is exactly a normalized nonnegative kernel certificate. -/
theorem hexagon_zero_iff_normalized_piece_kernel {r D : ℕ}
    (z : Fin r → Fin 3 → Point D) :
    (∃ x : HexagonDomain r, x ≠ 0 ∧ hexagonCayleyMap z x = 0) ↔
      ∃ s : Fin r → Fin 6, ∃ t : HexagonDomain r,
        HexNonnegative t ∧ hexParameterMass t = 1 ∧ hexPieceLinear z s t = 0 := by
  constructor
  · rintro ⟨x, hx, hz⟩
    obtain ⟨s, t, ht, he⟩ := exists_hexSectorArray x
    have hn : t ≠ 0 := by
      intro h
      rw [h, map_zero] at he
      exact hx he.symm
    have hm := hexParameterMass_pos t ht hn
    have hk : hexPieceLinear z s t = 0 := by
      rw [← hexagonCayleyMap_sector z s t ht, he]
      exact hz
    refine ⟨s, (hexParameterMass t)⁻¹ • t,
      ht.smul (inv_nonneg.mpr hm.le), ?_, ?_⟩
    · simp [map_smul, smul_eq_mul, ne_of_gt hm]
    · simp [map_smul, hk]
  · rintro ⟨s, t, ht, hm, hz⟩
    have hn : t ≠ 0 := by
      intro h
      simp [h] at hm
    refine ⟨hexSectorArray s t, ?_, ?_⟩
    · intro h
      apply hn
      apply hexSectorArray_injective s
      simpa using h
    · rw [hexagonCayleyMap_sector z s t ht]
      exact hz

/-- Nonnegative scaling preserves sectors and commutes with the concrete map. -/
theorem hexagonCayleyMap_nonneg_smul {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (x : HexagonDomain r) (a : ℝ) (ha : 0 ≤ a) :
    hexagonCayleyMap z (a • x) = a • hexagonCayleyMap z x := by
  obtain ⟨s, t, ht, rfl⟩ := exists_hexSectorArray x
  rw [← map_smul, hexagonCayleyMap_sector z s (a • t) (ht.smul ha),
    map_smul, hexagonCayleyMap_sector z s t ht]

end VCDimConvexBound
