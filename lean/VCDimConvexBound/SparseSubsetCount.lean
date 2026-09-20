import VCDimConvexBound.LabelCount
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A weighted count of sparse representative subsets

When M = 16k > 0, give a subset V weight 4^(M-|V|). Summing over all subsets
gives 5^M. Every sparse subset has weight at least 4^(15k), and
5^16 < 2^38 yields U < 2^(8k). This avoids logarithmic entropy estimates.
-/

namespace VCDimConvexBound

open scoped BigOperators

/-- A weighted binomial count for representative subsets. -/
theorem card_sparseSubsets_mul_weight_le (ι : Type*) [Fintype ι]
    (k : ℕ) (hcard : Fintype.card ι = 16 * k) :
    (sparseSubsets ι).card * 4 ^ (15 * k) ≤ 5 ^ (16 * k) := by
  classical
  calc
    (sparseSubsets ι).card * 4 ^ (15 * k) =
        ∑ V ∈ sparseSubsets ι, 4 ^ (15 * k) := by simp
    _ ≤ ∑ V ∈ sparseSubsets ι, 4 ^ (Fintype.card ι - V.card) := by
      apply Finset.sum_le_sum
      intro V hV
      have hs := mem_sparseSubsets V |>.mp hV
      apply Nat.pow_le_pow_right (by decide)
      omega
    _ ≤ ∑ V : Finset ι, 4 ^ (Fintype.card ι - V.card) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 5 ^ (16 * k) := by
      simpa [hcard] using Fintype.sum_pow_mul_eq_add_pow ι (1 : ℕ) 4

/-- Sparse subsets use strictly less than half the bit budget. -/
theorem card_sparseSubsets_lt_two_pow_half (ι : Type*) [Fintype ι]
    (k : ℕ) (hk : 0 < k) (hcard : Fintype.card ι = 16 * k) :
    (sparseSubsets ι).card < 2 ^ (8 * k) := by
  have hnum : 5 ^ (16 * k) < (2 : ℕ) ^ (38 * k) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  have heq : (2 : ℕ) ^ (38 * k) = 2 ^ (8 * k) * 4 ^ (15 * k) := by
    calc
      2 ^ (38 * k) = 2 ^ (8 * k + 2 * (15 * k)) := by congr 1; omega
      _ = 2 ^ (8 * k) * (2 ^ 2) ^ (15 * k) := by rw [pow_add, pow_mul 2 2]
      _ = _ := by norm_num
  have h := (card_sparseSubsets_mul_weight_le ι k hcard).trans_lt hnum
  rw [heq] at h
  exact Nat.lt_of_mul_lt_mul_right h

/-- A root-free form of the half-budget estimate. -/
theorem card_sparseSubsets_sq_lt (ι : Type*) [Fintype ι]
    (k : ℕ) (hk : 0 < k) (hcard : Fintype.card ι = 16 * k) :
    (sparseSubsets ι).card ^ 2 < 2 ^ Fintype.card ι := by
  calc
    (sparseSubsets ι).card ^ 2 < (2 ^ (8 * k)) ^ 2 :=
      Nat.pow_lt_pow_left (card_sparseSubsets_lt_two_pow_half ι k hk hcard) (by decide)
    _ = 2 ^ Fintype.card ι := by rw [hcard, ← pow_mul]; congr 1; omega

/-- The chosen additive grid has a positive cardinality divisible by sixteen. -/
theorem explicit_grid_card_eq_sixteen_mul (D : ℕ) (hD : 2 ≤ D) :
    ∃ k : ℕ, 0 < k ∧
      Fintype.card (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))) = 16 * k := by
  let e := 8 * (D + 1) ^ (D - 1) * D
  have hp : 0 < (D + 1) ^ (D - 1) := by positivity
  have he : 4 ≤ e := by dsimp [e]; nlinarith
  refine ⟨2 ^ (e - 4), by positivity, ?_⟩
  rw [card_grid, ← pow_mul]
  change 2 ^ e = 16 * 2 ^ (e - 4)
  calc
    2 ^ e = 2 ^ (4 + (e - 4)) := by congr 1; omega
    _ = _ := by rw [pow_add]; norm_num

/-- P7: the representative-subset factor is strictly below 2^(M/2). -/
theorem card_sparseSubsets_explicit_sq_lt (D : ℕ) (hD : 2 ≤ D) :
    (sparseSubsets (Grid D (2 ^ (8 * (D + 1) ^ (D - 1))))).card ^ 2 <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  obtain ⟨k, hk, hcard⟩ := explicit_grid_card_eq_sixteen_mul D hD
  simpa using card_sparseSubsets_sq_lt _ k hk hcard

end VCDimConvexBound
