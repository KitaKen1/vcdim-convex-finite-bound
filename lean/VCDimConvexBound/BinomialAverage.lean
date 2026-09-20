import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic

/-!
# A lower bound for an average of binomial coefficients

We use Jensen for the ordinary power function on nonnegative reals and
`Nat.pow_sub_le_descFactorial`. This avoids defining binomial coefficients
at real arguments. The loss of `s` in the average degree is sufficient for
the dense-fiber estimate under the assumption `δ * m ≥ 2 * s`.
-/

namespace VCDimConvexBound

open Finset

variable {β : Type*} [Fintype β] [Nonempty β]

/-- Jensen's inequality with uniform weights. -/
theorem power_mean_le (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) (s : ℕ) :
    ((∑ b, f b) / (Fintype.card β : ℝ)) ^ s ≤
      (∑ b, f b ^ s) / (Fintype.card β : ℝ) := by
  have hB : 0 < (Fintype.card β : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∑ _b : β, (Fintype.card β : ℝ)⁻¹ = 1 := by
    simp [hB.ne']
  have h := (convexOn_pow (𝕜 := ℝ) s).map_sum_le (t := univ)
    (w := fun _ : β => (Fintype.card β : ℝ)⁻¹) (p := f)
    (fun _ _ => inv_nonneg.mpr hB.le) hw (fun b _ => hf b)
  simp only [smul_eq_mul, ← mul_sum] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- If the average degree is at least `a + s`, its average binomial coefficient
is at least `a^s / s!`, stated without division by the factorial. -/
theorem power_le_factorial_mul_average_choose (d : β → ℕ) (s : ℕ) (a : ℝ)
    (ha : 0 ≤ a)
    (havg : a + s ≤ (∑ b, (d b : ℝ)) / (Fintype.card β : ℝ)) :
    a ^ s ≤ (s.factorial : ℝ) * (∑ b, ((d b).choose s : ℝ)) /
      (Fintype.card β : ℝ) := by
  let x : β → ℝ := fun b => (d b + 1 - s : ℕ)
  have hB : 0 < (Fintype.card β : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hx : ∀ b, 0 ≤ x b := fun _ => Nat.cast_nonneg _
  have hd : ∀ b, (d b : ℝ) ≤ x b + s := by
    intro b
    dsimp [x]
    exact_mod_cast (show d b ≤ (d b + 1 - s) + s by omega)
  have hsum : (∑ b, (d b : ℝ)) ≤
      (∑ b, x b) + (Fintype.card β : ℝ) * s := by
    simpa only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] using
      sum_le_sum (fun b (_ : b ∈ (univ : Finset β)) => hd b)
  have havg' := (le_div_iff₀ hB).mp havg
  have hax : a ≤ (∑ b, x b) / (Fintype.card β : ℝ) := by
    apply (le_div_iff₀ hB).mpr
    nlinarith
  have hchoose : ∀ b, x b ^ s ≤ (s.factorial : ℝ) * ((d b).choose s : ℝ) := by
    intro b
    have h := Nat.pow_sub_le_descFactorial (d b) s
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    dsimp [x]
    exact_mod_cast h
  calc
    a ^ s ≤ ((∑ b, x b) / (Fintype.card β : ℝ)) ^ s := pow_le_pow_left₀ ha hax s
    _ ≤ (∑ b, x b ^ s) / (Fintype.card β : ℝ) := power_mean_le x hx s
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hB.le
      simpa only [mul_sum] using
        sum_le_sum (fun b (_ : b ∈ (univ : Finset β)) => hchoose b)

end VCDimConvexBound
