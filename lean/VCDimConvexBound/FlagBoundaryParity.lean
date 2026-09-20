import VCDimConvexBound.FlagFaceCrossings

/-!
# The local coordinate-flag boundary identity

Under the explicit finite minor conditions, the zero-crossing indicator
of a simplex is the sum of positive-crossing indicators of all of its
codimension-one faces over ZMod 2. Empty slices are included. This is a
local matrix theorem; transport to the hexagon face chains and removal
of general position remain separate tasks.
-/

namespace VCDimConvexBound

open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

/-- A generic boundary face has at most one barycentric coordinate crossing. -/
theorem flagBoundaryPoint_unique {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (p : Fin (r + 2))
    (hdet : (sliceDeleteColumn (flagConstraintMatrix X) p).det ≠ 0)
    (x y : Fin (r + 2) → ℝ)
    (hx : flagCrossingPoint X x) (hy : flagCrossingPoint X y)
    (hxp : x p = 0) (hyp : y p = 0) : x = y := by
  have hx' := (flagConstraintMatrix_eq_rhs_iff X x).mpr ⟨hx.1, hx.2.1⟩
  have hy' := (flagConstraintMatrix_eq_rhs_iff X y).mpr ⟨hy.1, hy.2.1⟩
  have hk : flagConstraintMatrix X *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hx', hy', sub_self]
  have hp : (x - y) p = 0 := by simp [hxp, hyp]
  exact sub_eq_zero.mp (sliceMatrix_kernel_eq_zero_of_coord_zero
    (flagConstraintMatrix X) p hdet (x - y) hk hp)

/-- The local identity q = delta alpha, with one term per actual deleted-column
face and with no nonemptiness assumption on the slice. -/
theorem flag_local_boundary_parity {r : ℕ}
    (X : Matrix (Fin r) (Fin (r + 2)) ℝ) (z : Fin (r + 2) → ℝ)
    (hG : FlagSliceGeneric X z) :
    flagZeroBit (flagPrependRow z X) =
      ∑ i : Fin (r + 2), flagPositiveBit (X.submatrix id i.succAbove)
        (fun j => z (i.succAbove j)) := by
  by_cases hfeas : ∃ x, flagSlicePoint X x
  · obtain ⟨a, w, L, U, p, n, hLU, hpn, hline, hI, hLp, hUn,
      _, hboundary, hd, hL, hU⟩ := exists_flagSlice_interval X z hG hfeas
    have hLl := (hline (sliceCoeff a w L)).mpr ⟨L, rfl⟩
    have hUl := (hline (sliceCoeff a w U)).mpr ⟨U, rfl⟩
    have hl : flagCrossingPoint X (sliceCoeff a w L) :=
      ⟨hLl.1, hLl.2, (hI L).mpr ⟨le_rfl, hLU.le⟩⟩
    have hu : flagCrossingPoint X (sliceCoeff a w U) :=
      ⟨hUl.1, hUl.2, (hI U).mpr ⟨hLU.le, le_rfl⟩⟩
    have hface (i : Fin (r + 2)) : flagHasBoundaryCrossing X z i ↔
        (i = p ∧ 0 < sliceHeight a w z L) ∨ (i = n ∧ 0 < sliceHeight a w z U) := by
      constructor
      · rintro ⟨x, hx, hxi, hpos⟩
        obtain ⟨t, rfl⟩ := (hline x).mp ⟨hx.1, hx.2.1⟩
        obtain rfl | rfl := (hboundary t).mp ⟨hx.2.2, i, hxi⟩
        · exact Or.inl ⟨(hLp i).mp hxi, hpos⟩
        · exact Or.inr ⟨(hUn i).mp hxi, hpos⟩
      · rintro (⟨rfl, hpos⟩ | ⟨rfl, hpos⟩)
        · exact ⟨sliceCoeff a w L, hl, (hLp _).mpr rfl, hpos⟩
        · exact ⟨sliceCoeff a w U, hu, (hUn _).mpr rfl, hpos⟩
    have hbit (i : Fin (r + 2)) :
        (if flagHasBoundaryCrossing X z i then (1 : ZMod 2) else 0) =
          (if i = p then positiveBit (sliceHeight a w z L) else 0) +
          (if i = n then positiveBit (sliceHeight a w z U) else 0) := by
      rw [hface]
      by_cases hip : i = p
      · subst i
        simp [hpn, positiveBit]
      · by_cases hin : i = n
        · subst i
          simp [hip, positiveBit]
        · simp [hip, hin]
    have hcount : (∑ i : Fin (r + 2),
        flagPositiveBit (X.submatrix id i.succAbove) (fun j => z (i.succAbove j))) =
        positiveBit (sliceHeight a w z L) + positiveBit (sliceHeight a w z U) := by
      simp only [flagPositiveBit, flagPositiveCrossing_face_iff, hbit]
      rw [Finset.sum_add_distrib]
      simp
    have hex : (∃ t, sliceFeasible a w t ∧ sliceHeight a w z t = 0) ↔
        (∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) = 0) := by
      constructor
      · rintro ⟨t, ht, hz⟩
        have heq := (hline (sliceCoeff a w t)).mpr ⟨t, rfl⟩
        exact ⟨sliceCoeff a w t, ⟨heq.1, heq.2, ht⟩, hz⟩
      · rintro ⟨x, hx, hz⟩
        obtain ⟨t, rfl⟩ := (hline x).mp ⟨hx.1, hx.2.1⟩
        exact ⟨t, hx.2.2, hz⟩
    rw [hcount, flagZeroBit_prepend]
    have hpar := sliceHeight_endpoint_parity a w z hLU hI hd hL hU
    rw [hex] at hpar
    exact hpar.symm
  · have hz : ¬ ∃ x, flagCrossingPoint X x ∧ (∑ i, x i * z i) = 0 := by
      rintro ⟨x, hx, _⟩
      exact hfeas ⟨x, hx⟩
    have hf (i : Fin (r + 2)) : ¬ flagHasBoundaryCrossing X z i := by
      rintro ⟨x, hx, _, _⟩
      exact hfeas ⟨x, hx⟩
    simp [flagZeroBit_prepend, flagPositiveBit, flagPositiveCrossing_face_iff, hz, hf]

end VCDimConvexBound
