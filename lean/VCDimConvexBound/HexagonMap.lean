import VCDimConvexBound.HexagonWeights

/-!
# The continuous odd map produced by a hypothetical Sanyal counterexample

One hexagon per color supplies disjoint colorful weights. Their centered
Cayley difference is nonzero off the origin and takes values in a space of
dimension 2D-1. The topological assertion forbidding this map is not proved here.
-/

namespace VCDimConvexBound

open scoped BigOperators

abbrev HexagonDomain (r : ℕ) := Fin r → ℝ × ℝ

/-- Apply the three hexagon weights independently in each color. -/
noncomputable def hexCoeffs {r : ℕ} (x : HexagonDomain r) (e : Fin r × Fin 3) : ℝ :=
  hexWeight (x e.1) e.2

theorem continuous_hexCoeffs (r : ℕ) : Continuous (@hexCoeffs r) := by
  apply continuous_pi
  intro e
  exact ((continuous_apply e.2).comp continuous_hexWeight).comp (continuous_apply e.1)

/-- A nonzero input has positive total mass among the two coefficient families. -/
theorem hexCoeffs_total_pos {r : ℕ} (x : HexagonDomain r) (hx : x ≠ 0) :
    0 < (∑ e, hexCoeffs x e) + ∑ e, hexCoeffs (-x) e := by
  have ha : 0 ≤ ∑ e, hexCoeffs x e :=
    Finset.sum_nonneg (fun e _ => hexWeight_nonneg _ _)
  have hb : 0 ≤ ∑ e, hexCoeffs (-x) e :=
    Finset.sum_nonneg (fun e _ => hexWeight_nonneg _ _)
  by_contra hn
  have hle := le_of_not_gt hn
  have hsa : ∑ e, hexCoeffs x e = 0 := by linarith
  have hsb : ∑ e, hexCoeffs (-x) e = 0 := by linarith
  have hza := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => hexWeight_nonneg (x e.1) e.2)).mp hsa
  have hzb := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => hexWeight_nonneg ((-x) e.1) e.2)).mp hsb
  apply hx
  funext k
  exact eq_zero_of_hexWeight_eq_zero (x k)
    (fun j => hza (k, j) (Finset.mem_univ _)) (fun j => hzb (k, j) (Finset.mem_univ _))

/-- The concrete map into the ambient Cayley space. -/
noncomputable def hexagonCayleyMap {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (x : HexagonDomain r) : CayleySpace r D :=
  cayleyCenteredDifference z (hexCoeffs x) (hexCoeffs (-x))

theorem continuous_hexagonCayleyMap {r D : ℕ} (z : Fin r → Fin 3 → Point D) :
    Continuous (hexagonCayleyMap z) := by
  exact continuous_cayleyCenteredDifference z _ _ (continuous_hexCoeffs r)
    ((continuous_hexCoeffs r).comp continuous_neg)

theorem hexagonCayleyMap_neg {r D : ℕ} (z : Fin r → Fin 3 → Point D)
    (x : HexagonDomain r) : hexagonCayleyMap z (-x) = -hexagonCayleyMap z x := by
  simp only [hexagonCayleyMap, neg_neg]
  exact cayleyCenteredDifference_swap z _ _

/-- All combinatorial hypotheses of the centered-difference theorem are now supplied. -/
theorem hexagonCayleyMap_ne_zero {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (x : HexagonDomain r) (hx : x ≠ 0) : hexagonCayleyMap z x ≠ 0 := by
  exact cayleyCenteredDifference_ne_zero_of_colorful hr (by decide) z hz _ _
    (fun e => hexWeight_nonneg _ _) (fun e => hexWeight_nonneg _ _)
    (fun k j l => hexWeight_colorful (x k) j l)
    (fun k j l => hexWeight_colorful ((-x) k) j l)
    (fun e => hexWeight_disjoint (x e.1) e.2) (hexCoeffs_total_pos x hx)

/-- The actual target is the color-sum kernel, rather than the larger ambient space. -/
noncomputable def hexagonKernelMap {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (x : HexagonDomain r) :
    LinearMap.ker (cayleyColorSum r D) :=
  ⟨hexagonCayleyMap z x, cayleyCenteredDifference_mem_ker hr (by decide) z _ _⟩

theorem continuous_hexagonKernelMap {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) : Continuous (hexagonKernelMap hr z) :=
  (continuous_hexagonCayleyMap z).subtype_mk _

theorem hexagonKernelMap_neg {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (x : HexagonDomain r) :
    hexagonKernelMap hr z (-x) = -hexagonKernelMap hr z x := by
  apply Subtype.ext
  exact hexagonCayleyMap_neg z x

theorem hexagonKernelMap_ne_zero {r D : ℕ} (hr : 0 < r)
    (z : Fin r → Fin 3 → Point D) (hz : ConvexIndependent ℝ (gridSum z))
    (x : HexagonDomain r) (hx : x ≠ 0) : hexagonKernelMap hr z x ≠ 0 := by
  intro h
  exact hexagonCayleyMap_ne_zero hr z hz x hx (congrArg Subtype.val h)

/-- There are exactly two real input coordinates per color. -/
theorem finrank_hexagonDomain (r : ℕ) : Module.finrank ℝ (HexagonDomain r) = 2 * r := by
  simp [HexagonDomain, Module.finrank_pi_fintype, Module.finrank_prod, Nat.mul_comm]

end VCDimConvexBound
