import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The nonnegative part of an affine line

This is the one-dimensional inequality step for the coordinate-flag route.
It does not construct the affine line from the coordinate equations or prove
that the required general-position conditions hold for vertex images.
-/

namespace VCDimConvexBound

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The coefficient vector on a parameterized affine line. -/
def sliceCoeff (a w : ι → ℝ) (t : ℝ) (i : ι) : ℝ := a i + t * w i

/-- Parameters whose coefficient vector is in the nonnegative orthant. -/
def sliceFeasible (a w : ι → ℝ) (t : ℝ) : Prop := ∀ i, 0 ≤ sliceCoeff a w t i

/-- No two distinct coordinates vanish at the same parameter. Later this
condition must be deduced from the augmented general-position minors. -/
def sliceNoDoubleZero (a w : ι → ℝ) : Prop :=
  ∀ i j t, sliceCoeff a w t i = 0 → sliceCoeff a w t j = 0 → i = j

theorem sliceCoeff_nonneg_of_pos {a w t : ℝ} (hw : 0 < w) :
    0 ≤ a + t * w ↔ -a / w ≤ t := by
  rw [div_le_iff₀ hw]
  constructor <;> intro h <;> linarith

theorem sliceCoeff_nonneg_of_neg {a w t : ℝ} (hw : w < 0) :
    0 ≤ a + t * w ↔ t ≤ -a / w := by
  rw [le_div_iff_of_neg hw]
  constructor <;> intro h <;> linarith

theorem sliceCoeff_at_root (a w : ℝ) (hw : w ≠ 0) :
    a + (-a / w) * w = 0 := by
  rw [div_mul_cancel₀ _ hw]
  exact add_neg_cancel a

/-- A nonzero direction tangent to the mass-one hyperplane has both signs. -/
theorem sliceDirection_has_both_signs (w : ι → ℝ) (hsum : ∑ i, w i = 0)
    (hne : w ≠ 0) : (∃ i, 0 < w i) ∧ (∃ i, w i < 0) := by
  have hex : ∃ i ∈ Finset.univ, w i ≠ 0 := by
    by_contra! h
    apply hne
    funext i
    exact h i (Finset.mem_univ i)
  obtain ⟨p, _, hp⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero w hsum hex
  have hneg : ∑ i, -w i = 0 := by rw [Finset.sum_neg_distrib, hsum, neg_zero]
  have hexneg : ∃ i ∈ Finset.univ, -w i ≠ 0 := by
    obtain ⟨i, hi, hwi⟩ := hex
    exact ⟨i, hi, neg_ne_zero.mpr hwi⟩
  obtain ⟨n, _, hn⟩ :=
    Finset.exists_pos_of_sum_zero_of_exists_nonzero (fun i => -w i) hneg hexneg
  exact ⟨⟨p, hp⟩, ⟨n, by linarith⟩⟩

/-- Choose the active lower and upper constraints. The endpoints are the
maximum positive-slope root and the minimum negative-slope root. This also
covers an empty feasible set, when the lower root exceeds the upper root. -/
theorem exists_slice_interval (a w : ι → ℝ)
    (hpos : ∃ i, 0 < w i) (hneg : ∃ i, w i < 0)
    (hzero : ∀ i, w i = 0 → 0 ≤ a i) :
    ∃ p n : ι, 0 < w p ∧ w n < 0 ∧
      (∀ i, 0 < w i → -a i / w i ≤ -a p / w p) ∧
      (∀ i, w i < 0 → -a n / w n ≤ -a i / w i) ∧
      (∀ t, sliceFeasible a w t ↔ -a p / w p ≤ t ∧ t ≤ -a n / w n) := by
  classical
  let P := Finset.univ.filter fun i => 0 < w i
  let N := Finset.univ.filter fun i => w i < 0
  have hP : P.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hN : N.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨p, hp, hpmax⟩ := P.exists_max_image (fun i => -a i / w i) hP
  obtain ⟨n, hn, hnmin⟩ := N.exists_min_image (fun i => -a i / w i) hN
  have hwp : 0 < w p := (Finset.mem_filter.mp hp).2
  have hwn : w n < 0 := (Finset.mem_filter.mp hn).2
  have hpmax' : ∀ i, 0 < w i → -a i / w i ≤ -a p / w p := by
    intro i hi
    exact hpmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hnmin' : ∀ i, w i < 0 → -a n / w n ≤ -a i / w i := by
    intro i hi
    exact hnmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  refine ⟨p, n, hwp, hwn, hpmax', hnmin', ?_⟩
  intro t
  constructor
  · intro ht
    exact ⟨(sliceCoeff_nonneg_of_pos hwp).mp (ht p),
      (sliceCoeff_nonneg_of_neg hwn).mp (ht n)⟩
  · rintro ⟨hL, hU⟩ i
    rcases lt_trichotomy (w i) 0 with hi | hi | hi
    · exact (sliceCoeff_nonneg_of_neg hi).mpr (hU.trans (hnmin' i hi))
    · simpa [sliceCoeff, hi] using hzero i hi
    · exact (sliceCoeff_nonneg_of_pos hi).mpr ((hpmax' i hi).trans hL)

/-- The closed-interval formulation, including the active endpoint coordinates. -/
theorem exists_slice_interval_endpoints (a w : ι → ℝ)
    (hsum : ∑ i, w i = 0) (hne : w ≠ 0)
    (hzero : ∀ i, w i = 0 → 0 ≤ a i) :
    ∃ L U : ℝ, (∀ t, sliceFeasible a w t ↔ L ≤ t ∧ t ≤ U) ∧
      (∃ p, 0 < w p ∧ sliceCoeff a w L p = 0) ∧
      (∃ n, w n < 0 ∧ sliceCoeff a w U n = 0) := by
  obtain ⟨hpos, hneg⟩ := sliceDirection_has_both_signs w hsum hne
  obtain ⟨p, n, hp, hn, _, _, hI⟩ := exists_slice_interval a w hpos hneg hzero
  exact ⟨-a p / w p, -a n / w n, hI,
    ⟨p, hp, sliceCoeff_at_root (a p) (w p) (ne_of_gt hp)⟩,
    ⟨n, hn, sliceCoeff_at_root (a n) (w n) (ne_of_lt hn)⟩⟩

/-- Along a mass-preserving direction the coefficient sum is constant. -/
theorem sum_sliceCoeff (a w : ι → ℝ) (t : ℝ) (hw : ∑ i, w i = 0) :
    ∑ i, sliceCoeff a w t i = ∑ i, a i := by
  simp [sliceCoeff, Finset.sum_add_distrib, ← Finset.mul_sum, hw]

omit [Fintype ι] in
/-- With nonzero slope, a nonnegative affine function at both endpoints
is strictly positive at every interior parameter. -/
theorem sliceCoeff_pos_between (a w : ι → ℝ) {L U t : ℝ}
    (hL : sliceFeasible a w L) (hU : sliceFeasible a w U)
    (hLt : L < t) (htU : t < U) (hw : ∀ i, w i ≠ 0) :
    ∀ i, 0 < sliceCoeff a w t i := by
  intro i
  have hLi := hL i
  have hUi := hU i
  unfold sliceCoeff at *
  rcases lt_or_gt_of_ne (hw i) with hi | hi
  · have hmul := mul_pos (sub_pos.mpr htU) (neg_pos.mpr hi)
    nlinarith
  · have hmul := mul_pos (sub_pos.mpr hLt) hi
    nlinarith

/-- Under explicit genericity assumptions, every nonempty feasible interval
has two distinct endpoints, exactly one zero coordinate at each endpoint,
and strictly positive coordinates at every interior parameter. -/
theorem exists_generic_slice_endpoints (a w : ι → ℝ)
    (hsum : ∑ i, w i = 0) (hne : w ≠ 0)
    (hw : ∀ i, w i ≠ 0) (hG : sliceNoDoubleZero a w)
    (hfeas : ∃ t, sliceFeasible a w t) :
    ∃ L U : ℝ, ∃ p n : ι,
      L < U ∧ p ≠ n ∧ 0 < w p ∧ w n < 0 ∧
      (∀ t, sliceFeasible a w t ↔ L ≤ t ∧ t ≤ U) ∧
      (∀ i, sliceCoeff a w L i = 0 ↔ i = p) ∧
      (∀ i, sliceCoeff a w U i = 0 ↔ i = n) ∧
      (∀ t, L < t → t < U → ∀ i, 0 < sliceCoeff a w t i) ∧
      (∀ t, (sliceFeasible a w t ∧ ∃ i, sliceCoeff a w t i = 0) ↔
        t = L ∨ t = U) := by
  obtain ⟨L, U, hI, ⟨p, hp, hLp⟩, ⟨n, hn, hUn⟩⟩ :=
    exists_slice_interval_endpoints a w hsum hne (fun i hi => (hw i hi).elim)
  have hpn : p ≠ n := by rintro rfl; linarith
  have hLU : L < U := by
    obtain ⟨t, ht⟩ := hfeas
    have hle : L ≤ U := (hI t |>.mp ht).1.trans (hI t |>.mp ht).2
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact hpn (hG p n L hLp (heq.symm ▸ hUn))
  have hL : sliceFeasible a w L := (hI L).mpr ⟨le_rfl, hLU.le⟩
  have hU : sliceFeasible a w U := (hI U).mpr ⟨hLU.le, le_rfl⟩
  have hpos : ∀ t, L < t → t < U → ∀ i, 0 < sliceCoeff a w t i := by
    intro t htL htU
    exact sliceCoeff_pos_between a w hL hU htL htU hw
  refine ⟨L, U, p, n, hLU, hpn, hp, hn, hI, ?_, ?_, hpos, ?_⟩
  · intro i
    exact ⟨fun hi => hG i p L hi hLp, fun hi => hi ▸ hLp⟩
  · intro i
    exact ⟨fun hi => hG i n U hi hUn, fun hi => hi ▸ hUn⟩
  · intro t
    constructor
    · rintro ⟨ht, i, hi⟩
      obtain ⟨htL, htU⟩ := (hI t).mp ht
      by_contra! h
      have hposi := hpos t (lt_of_le_of_ne htL (Ne.symm h.1))
        (lt_of_le_of_ne htU h.2) i
      linarith
    · rintro (rfl | rfl)
      · exact ⟨hL, p, hLp⟩
      · exact ⟨hU, n, hUn⟩

end VCDimConvexBound
