import VCDimConvexBound.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import VCDimConvexBound.BinomialAverage

/-!
# Common fibers of a dense finite relation

The first step of the dense-box argument counts pairs `(A, b)`, where `A`
has `s` elements and every `a ∈ A` is related to `b`.
-/

namespace VCDimConvexBound
namespace DenseFiber

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
variable (R : α → β → Prop) [DecidableRel R]

/-- The left fiber over a right vertex. -/
def fiber (b : β) : Finset α := univ.filter fun a => R a b

/-- The right vertices related to every member of `A`. -/
def common (A : Finset α) : Finset β := univ.filter fun b => ∀ a ∈ A, R a b

omit [Fintype β] [DecidableEq α] in
@[simp] theorem mem_fiber (a : α) (b : β) : a ∈ fiber R b ↔ R a b := by
  simp [fiber]

@[simp] theorem mem_common (A : Finset α) (b : β) :
    b ∈ common R A ↔ ∀ a ∈ A, R a b := by
  simp [common]

omit [Fintype β] in
theorem powersetCard_fiber (s : ℕ) (b : β) :
    (fiber R b).powersetCard s =
      (univ.powersetCard s).filter (fun A : Finset α => ∀ a ∈ A, R a b) := by
  ext A
  simp only [mem_powersetCard, mem_filter, subset_univ, true_and]
  have h : A ⊆ fiber R b ↔ ∀ a ∈ A, R a b := by simp [subset_iff]
  rw [h]
  exact and_comm

/-- Count complete stars by the right vertex or by their left vertex set. -/
theorem sum_choose_eq_sum_common (s : ℕ) :
    ∑ b : β, (fiber R b).card.choose s =
      ∑ A ∈ (univ : Finset α).powersetCard s, (common R A).card := by
  simp_rw [← card_powersetCard, powersetCard_fiber, common, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- One common fiber is at least the average, in an integer form without division. -/
theorem exists_common_ge_average (s : ℕ) (hs : s ≤ Fintype.card α) :
    ∃ A : Finset α, A.card = s ∧
      (∑ b : β, (fiber R b).card.choose s) ≤
        (Fintype.card α).choose s * (common R A).card := by
  have hne : ((univ : Finset α).powersetCard s).Nonempty := by
    apply card_pos.mp
    simpa only [card_powersetCard, card_univ] using Nat.choose_pos hs
  obtain ⟨A, hA, hmax⟩ :=
    ((univ : Finset α).powersetCard s).exists_max_image (fun A => (common R A).card) hne
  refine ⟨A, (mem_powersetCard.mp hA).2, ?_⟩
  rw [sum_choose_eq_sum_common]
  calc
    _ ≤ ∑ _B ∈ (univ : Finset α).powersetCard s, (common R A).card :=
      sum_le_sum hmax
    _ = _ := by simp

/-- A dense relation contains an `s`-element left set with a common fiber of
density at least `(δ / 2)^s`, with no unproved analytic or counting input. -/
theorem exists_common_of_density [Nonempty α] [Nonempty β]
    (s : ℕ) (hs : s ≤ Fintype.card α) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlarge : 2 * (s : ℝ) ≤ δ * Fintype.card α)
    (hdensity : δ * (Fintype.card α : ℝ) * Fintype.card β ≤
      ∑ b : β, ((fiber R b).card : ℝ)) :
    ∃ A : Finset α, A.card = s ∧
      (δ / 2) ^ s * (Fintype.card β : ℝ) ≤ (common R A).card := by
  obtain ⟨A, hA, havg⟩ := exists_common_ge_average R s hs
  refine ⟨A, hA, ?_⟩
  have hM : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hB : 0 < (Fintype.card β : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hpow := power_le_factorial_mul_average_choose
    (fun b => (fiber R b).card) s (δ * Fintype.card α / 2)
    (by positivity) (by
      apply (le_div_iff₀ hB).mpr
      calc
        _ ≤ δ * (Fintype.card α : ℝ) * Fintype.card β :=
          mul_le_mul_of_nonneg_right (by linarith) hB.le
        _ ≤ _ := hdensity)
  have havgR : (∑ b : β, ((fiber R b).card.choose s : ℝ)) ≤
      ((Fintype.card α).choose s : ℝ) * (common R A).card := by
    exact_mod_cast havg
  have hfactor : (s.factorial : ℝ) * ((Fintype.card α).choose s : ℝ) ≤
      (Fintype.card α : ℝ) ^ s := by
    have h := Nat.descFactorial_le_pow (Fintype.card α) s
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast h
  have htotal : (δ * Fintype.card α / 2) ^ s * (Fintype.card β : ℝ) ≤
      (Fintype.card α : ℝ) ^ s * (common R A).card := by
    calc
      _ ≤ (s.factorial : ℝ) * ∑ b : β, ((fiber R b).card.choose s : ℝ) :=
        (le_div_iff₀ hB).mp hpow
      _ ≤ (s.factorial : ℝ) *
          (((Fintype.card α).choose s : ℝ) * (common R A).card) :=
        mul_le_mul_of_nonneg_left havgR (Nat.cast_nonneg _)
      _ = ((s.factorial : ℝ) * (Fintype.card α).choose s) * (common R A).card :=
        (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _)
  apply (mul_le_mul_iff_right₀ (pow_pos hM s)).mp
  calc
    (Fintype.card α : ℝ) ^ s * ((δ / 2) ^ s * Fintype.card β) =
        (δ * Fintype.card α / 2) ^ s * (Fintype.card β : ℝ) := by
      rw [show δ * (Fintype.card α : ℝ) / 2 = (Fintype.card α : ℝ) * (δ / 2) by ring,
        mul_pow]
      ring
    _ ≤ _ := htotal

end DenseFiber
end VCDimConvexBound
