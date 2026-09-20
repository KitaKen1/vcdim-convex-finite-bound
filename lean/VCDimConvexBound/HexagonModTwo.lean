import VCDimConvexBound.HexagonComplex
import Mathlib.Data.ZMod.Basic

/-!
# The mod-two boundary of the hexagon join

Boundary incidences of the facets pair across adjacent sectors. The pairing
is a fixed-point-free involution preserving the deleted face. Hence the sum
of all facet boundaries is zero over ZMod 2. This is the actual deletion
boundary on finite vertex sets; it is not yet an obstruction to an odd map.
-/

namespace VCDimConvexBound

open scoped BigOperators

abbrev HexBoundaryIncidence (r : ℕ) := (Fin r → Fin 6) × (Fin r × Bool)

/-- Cross the face obtained by deleting one endpoint of an edge. -/
def hexBoundaryMate {r : ℕ} (i : HexBoundaryIncidence r) : HexBoundaryIncidence r :=
  if i.2.2 then
    (Function.update i.1 i.2.1 (hexPrev (i.1 i.2.1)), (i.2.1, false))
  else
    (Function.update i.1 i.2.1 (hexNext (i.1 i.2.1)), (i.2.1, true))

theorem hexBoundaryMate_involutive (r : ℕ) :
    Function.Involutive (@hexBoundaryMate r) := by
  rintro ⟨s, k, b⟩
  cases b <;> simp [hexBoundaryMate, hexPrev_next, hexNext_prev]

theorem hexBoundaryMate_ne_self {r : ℕ} (i : HexBoundaryIncidence r) :
    hexBoundaryMate i ≠ i := by
  rcases i with ⟨s, k, b⟩
  intro h
  have hb := congrArg (fun i : HexBoundaryIncidence r => i.2.2) h
  cases b <;> simp [hexBoundaryMate] at hb

/-- Both incidences in a pair describe exactly the same boundary face. -/
theorem hexRidge_boundaryMate {r : ℕ} (i : HexBoundaryIncidence r) :
    hexRidge (hexBoundaryMate i).1 (hexBoundaryMate i).2 = hexRidge i.1 i.2 := by
  rcases i with ⟨s, k, b⟩
  ext v
  rw [mem_hexRidge, mem_hexRidge]
  by_cases hv : v.1 = k
  · cases b <;> simp [hexBoundaryMate, hv, hexNext_prev]
  · cases b <;> simp [hexBoundaryMate, hv, mem_hexFacet]

/-- Finite mod-two chains, including the empty face for the augmented boundary. -/
abbrev HexModTwoChain (r : ℕ) := Finset (HexVertex r) → ZMod 2

/-- The basis chain of a finite vertex set. -/
def hexFaceBasis {r : ℕ} (t : Finset (HexVertex r)) : HexModTwoChain r :=
  fun f => if t = f then 1 else 0

/-- The usual mod-two simplicial boundary, deleting each vertex once. -/
noncomputable def hexChainBoundary (r : ℕ) : HexModTwoChain r →ₗ[ZMod 2] HexModTwoChain r where
  toFun c := ∑ f : Finset (HexVertex r), c f • ∑ v ∈ f, hexFaceBasis (f.erase v)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [smul_smul, Finset.smul_sum]

theorem hexChainBoundary_basis {r : ℕ} (t : Finset (HexVertex r)) :
    hexChainBoundary r (hexFaceBasis t) = ∑ v ∈ t, hexFaceBasis (t.erase v) := by
  simp [hexChainBoundary, hexFaceBasis]

/-- The boundary formula for the actual 2r-vertex simplex of a sector. -/
theorem hexChainBoundary_facet {r : ℕ} (s : Fin r → Fin 6) :
    hexChainBoundary r (hexFaceBasis (hexFacet s)) =
      ∑ e : Fin r × Bool, hexFaceBasis (hexRidge s e) := by
  rw [hexChainBoundary_basis]
  change (∑ v ∈ Finset.univ.image (hexFacetVertex s),
    hexFaceBasis ((hexFacet s).erase v)) = _
  rw [Finset.sum_image]
  · rfl
  · exact fun a _ b _ h => hexFacetVertex_injective s h

/-- In characteristic two, the two copies of every boundary face cancel. -/
theorem sum_hexRidge_basis_eq_zero (r : ℕ) :
    (∑ i : HexBoundaryIncidence r, hexFaceBasis (hexRidge i.1 i.2)) = 0 := by
  apply Finset.sum_ninvolution hexBoundaryMate
  · intro i
    rw [hexRidge_boundaryMate]
    funext f
    simp only [Pi.add_apply, Pi.zero_apply, hexFaceBasis]
    split_ifs
    · exact (show (1 + 1 : ZMod 2) = 0 from by decide)
    · exact zero_add 0
  · intro i _
    exact hexBoundaryMate_ne_self i
  · intro i
    exact Finset.mem_univ _
  · exact hexBoundaryMate_involutive r

/-- The sum of all sector simplices is a cycle for the deletion boundary. -/
theorem hex_fundamental_boundary_eq_zero (r : ℕ) :
    hexChainBoundary r (∑ s : Fin r → Fin 6, hexFaceBasis (hexFacet s)) = 0 := by
  rw [map_sum]
  simp_rw [hexChainBoundary_facet]
  simpa only [Fintype.sum_prod_type] using sum_hexRidge_basis_eq_zero r

/-- The cycle is a nonzero chain, not cancellation of duplicate facets. -/
theorem hex_fundamental_chain_ne_zero (r : ℕ) :
    (∑ s : Fin r → Fin 6, hexFaceBasis (hexFacet s)) ≠ 0 := by
  intro h
  have he := congrFun h (hexFacet (fun _ : Fin r => (0 : Fin 6)))
  simp [Finset.sum_apply, hexFaceBasis, (hexFacet_injective r).eq_iff] at he

/-- A half of one hexagon has precisely its two antipodal endpoints as boundary. -/
theorem hex_half_cycle_boundary (v : Fin 6) :
    (∑ s ∈ ({0, 1, 2} : Finset (Fin 6)),
      ((if v = s then 1 else 0) + (if v = hexNext s then 1 else 0) : ZMod 2)) =
      (if v = 0 then 1 else 0) + (if v = 3 then 1 else 0) := by
  fin_cases v <;> decide

end VCDimConvexBound
