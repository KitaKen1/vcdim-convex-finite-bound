/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import VCDimConvexBound.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A small counterexample to the convex additive-VC₂ bound in R3Euclidean

This ports the v1 certificate to the pinned Formal Conjectures v4.33.1 environment.  It kernel-checks a convex
polyhedron in `R3Euclidean`, defined by six halfspaces, whose four-point additive grid
realizes all sixteen membership patterns under translation.  Consequently, its
additive `VC₂` dimension is not at most one.

All coordinates and halfspace coefficients in the certificate are integers.
-/

open scoped BigOperators

local notation "R3Euclidean" => EuclideanSpace ℝ (Fin 3)

namespace VCDimConvexBound.Regression.Counterexample

abbrev R3 := Fin 3 → ℝ

private def point (x y z : ℝ) : R3 := ![x, y, z]

private def lin (a b c : ℝ) (p : R3) : ℝ :=
  a * p 0 + b * p 1 + c * p 2

private def halfspace (a b c d : ℝ) : Set R3 :=
  {p | lin a b c p ≤ d}

private def C : Set R3 :=
  halfspace (-4) 1 0 25 ∩
    halfspace (-2) (-4) 3 43 ∩
    halfspace (-2) 4 (-1) 12 ∩
    halfspace 2 2 3 48 ∩
    halfspace 3 (-4) 0 15 ∩
    halfspace 4 (-1) 0 28

private lemma isLinearMap_lin (a b c : ℝ) : IsLinearMap ℝ (lin a b c) := by
  constructor
  · intro p q
    simp only [lin, Pi.add_apply]
    ring
  · intro r p
    simp only [lin, Pi.smul_apply, smul_eq_mul]
    ring

private lemma convex_halfspace (a b c d : ℝ) : Convex ℝ (halfspace a b c d) := by
  exact convex_halfSpace_le (isLinearMap_lin a b c) d

private lemma convex_C : Convex ℝ C := by
  simpa only [C] using
    (((((convex_halfspace (-4) 1 0 25).inter
      (convex_halfspace (-2) (-4) 3 43)).inter
      (convex_halfspace (-2) 4 (-1) 12)).inter
      (convex_halfspace 2 2 3 48)).inter
      (convex_halfspace 3 (-4) 0 15)).inter
      (convex_halfspace 4 (-1) 0 28)

private def i00 : Fin 2 → Fin 2 := ![0, 0]
private def i10 : Fin 2 → Fin 2 := ![1, 0]
private def i01 : Fin 2 → Fin 2 := ![0, 1]
private def i11 : Fin 2 → Fin 2 := ![1, 1]

private def I : Fin 4 → (Fin 2 → Fin 2) := ![i00, i10, i01, i11]

private def Z : Fin 4 → R3 := ![
  point 0 0 0,
  point 1 0 0,
  point 0 1 0,
  point 1 1 0]

/-- The translating vector for the subset `s`.

The four membership tests are arranged in descending bit significance:
`i11`, `i01`, `i10`, `i00`.  The sixteen leaves are exactly the translations
for masks `1111` down to `0000`.
-/
private noncomputable def y (s : Set (Fin 2 → Fin 2)) : R3 := by
  classical
  exact
    if i11 ∈ s then
      if i01 ∈ s then
        if i10 ∈ s then
          if i00 ∈ s then point 0 0 0       -- 1111
          else point (-5) (-5) 5           -- 1110
        else
          if i00 ∈ s then point 2 (-2) 0    -- 1101
          else point 0 (-4) 0               -- 1100
      else
        if i10 ∈ s then
          if i00 ∈ s then point (-1) 2 0    -- 1011
          else point (-7) (-1) 0            -- 1010
        else
          if i00 ∈ s then point 8 7 2       -- 1001
          else point (-3) (-6) 6            -- 1000
    else
      if i01 ∈ s then
        if i10 ∈ s then
          if i00 ∈ s then point 6 6 7       -- 0111
          else point 0 0 15                 -- 0110
        else
          if i00 ∈ s then point 7 2 0       -- 0101
          else point 2 (-3) 0               -- 0100
      else
        if i10 ∈ s then
          if i00 ∈ s then point (-1) 2 (-1) -- 0011
          else point (-2) 2 (-1)            -- 0010
        else
          if i00 ∈ s then point 6 7 7       -- 0001
          else point (-1) 3 (-1)            -- 0000

private lemma mem_y_add_Z_0_iff (s : Set (Fin 2 → Fin 2)) :
    y s + Z 0 ∈ C ↔ i00 ∈ s := by
  classical
  by_cases h00 : i00 ∈ s <;>
    by_cases h10 : i10 ∈ s <;>
    by_cases h01 : i01 ∈ s <;>
    by_cases h11 : i11 ∈ s <;>
    norm_num [y, Z, C, halfspace, lin, point, Matrix.cons_val_two,
      h00, h10, h01, h11]

private lemma mem_y_add_Z_1_iff (s : Set (Fin 2 → Fin 2)) :
    y s + Z 1 ∈ C ↔ i10 ∈ s := by
  classical
  by_cases h00 : i00 ∈ s <;>
    by_cases h10 : i10 ∈ s <;>
    by_cases h01 : i01 ∈ s <;>
    by_cases h11 : i11 ∈ s <;>
    norm_num [y, Z, C, halfspace, lin, point, Matrix.cons_val_two,
      h00, h10, h01, h11]

private lemma mem_y_add_Z_2_iff (s : Set (Fin 2 → Fin 2)) :
    y s + Z 2 ∈ C ↔ i01 ∈ s := by
  classical
  by_cases h00 : i00 ∈ s <;>
    by_cases h10 : i10 ∈ s <;>
    by_cases h01 : i01 ∈ s <;>
    by_cases h11 : i11 ∈ s <;>
    norm_num [y, Z, C, halfspace, lin, point, Matrix.cons_val_two,
      h00, h10, h01, h11]

private lemma mem_y_add_Z_3_of_mem (s : Set (Fin 2 → Fin 2))
    (h11 : i11 ∈ s) : y s + Z 3 ∈ C := by
  classical
  by_cases h01 : i01 ∈ s <;>
    by_cases h10 : i10 ∈ s <;>
    by_cases h00 : i00 ∈ s <;>
    norm_num [y, Z, C, halfspace, lin, point, Matrix.cons_val_two,
      Matrix.cons_val_three,
      h00, h10, h01, h11]

private lemma mem_y_add_Z_3_of_not_mem (s : Set (Fin 2 → Fin 2))
    (h11 : i11 ∉ s) : y s + Z 3 ∉ C := by
  classical
  by_cases h01 : i01 ∈ s <;>
    by_cases h10 : i10 ∈ s <;>
    by_cases h00 : i00 ∈ s <;>
    norm_num [y, Z, C, halfspace, lin, point, Matrix.cons_val_two,
      Matrix.cons_val_three,
      h00, h10, h01, h11]

private lemma mem_y_add_Z_3_iff (s : Set (Fin 2 → Fin 2)) :
    y s + Z 3 ∈ C ↔ i11 ∈ s := by
  by_cases h11 : i11 ∈ s
  · exact ⟨fun _ ↦ h11, fun _ ↦ mem_y_add_Z_3_of_mem s h11⟩
  · exact ⟨fun h ↦ (mem_y_add_Z_3_of_not_mem s h11 h).elim, fun h ↦ (h11 h).elim⟩

private lemma mem_y_add_Z_iff (s : Set (Fin 2 → Fin 2)) (j : Fin 4) :
    y s + Z j ∈ C ↔ I j ∈ s := by
  fin_cases j
  · simpa [I] using mem_y_add_Z_0_iff s
  · simpa [I] using mem_y_add_Z_1_iff s
  · simpa [I] using mem_y_add_Z_2_iff s
  · simpa [I] using mem_y_add_Z_3_iff s

private def code (i : Fin 2 → Fin 2) : Fin 4 :=
  ⟨(i 0).val + 2 * (i 1).val, by omega⟩

private lemma I_code (i : Fin 2 → Fin 2) : I (code i) = i := by
  generalize h0 : i 0 = a
  generalize h1 : i 1 = b
  fin_cases a <;> fin_cases b
  all_goals
    funext k
    fin_cases k <;> apply Fin.ext <;> simp [I, code, i00, i10, i01, i11, h0, h1]

private def x : Fin 2 → Fin 2 → R3 := ![
  ![point 0 0 0, point 1 0 0],
  ![point 0 0 0, point 0 1 0]]

private lemma sum_x_eq_Z (i : Fin 2 → Fin 2) :
    (∑ k, x k (i k)) = Z (code i) := by
  generalize h0 : i 0 = a
  generalize h1 : i 1 = b
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_two, x, Z, point, code, h0, h1]

private lemma shattering_certificate
    (i : Fin 2 → Fin 2) (s : Set (Fin 2 → Fin 2)) :
    y s + ∑ k, x k (i k) ∈ C ↔ i ∈ s := by
  rw [sum_x_eq_Z, mem_y_add_Z_iff, I_code]

private noncomputable abbrev toCoords : R3Euclidean ≃ₗ[ℝ] R3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv

/-- A convex polyhedron in `R3Euclidean` whose additive `VC₂` dimension is not at most one. -/
theorem exists_convex_r3_not_hasAddVCNDimAtMost_two_one :
    ∃ C : Set R3Euclidean, Convex ℝ C ∧ ¬ HasAddVCNDimAtMost C 2 1 := by
  refine ⟨toCoords ⁻¹' C, convex_C.linear_preimage toCoords.toLinearMap, ?_⟩
  intro h
  apply h (fun k j ↦ toCoords.symm (x k j)) (fun s ↦ toCoords.symm (y s))
  intro i s
  change
    toCoords (toCoords.symm (y s) + ∑ k, toCoords.symm (x k (i k))) ∈ C ↔ i ∈ s
  simpa only [map_add, map_sum, LinearEquiv.apply_symm_apply] using
    shattering_certificate i s

/-- The negation of `hasAddVCNDimAtMost_two_one_of_convex_r3`. -/
theorem not_hasAddVCNDimAtMost_two_one_of_convex_r3 :
    ¬ (∀ {C : Set R3Euclidean} (_hC : Convex ℝ C),
      HasAddVCNDimAtMost C 2 1) := by
  intro h
  obtain ⟨C, hC, hnot⟩ := exists_convex_r3_not_hasAddVCNDimAtMost_two_one
  exact hnot (h hC)



/-- The same certificate in the coordinate type used by the current FC declarations. -/
theorem exists_convex_coordinate_not_hasAddVCNDimAtMost_two_one :
    ∃ C : Set (Point 3), Convex ℝ C ∧ ¬ HasAddVCNDimAtMost C 2 1 := by
  exact ⟨C, convex_C, fun h => h x y shattering_certificate⟩

end VCDimConvexBound.Regression.Counterexample
