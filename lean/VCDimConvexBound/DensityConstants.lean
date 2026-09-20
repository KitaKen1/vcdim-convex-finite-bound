import VCDimConvexBound.DenseBox

/-!
# The explicit parameters for the dense-box lemma

Starting with density `1/16`, let `a₀ = 4` and `aⱼ₊₁ = s(aⱼ + 1)`.
The estimate `aⱼ + 2 ≤ 6sʲ` suffices to keep all common-fiber steps valid
when `s = D + 1` and `m = 2^(8s^(D-1))`.
-/

namespace VCDimConvexBound

/-- The exponent in the reciprocal-power density lower bound. -/
def densityExponent (s : ℕ) : ℕ → ℕ
  | 0 => 4
  | j + 1 => s * (densityExponent s j + 1)

theorem densityExponent_add_two_le (s : ℕ) (hs : 2 ≤ s) (j : ℕ) :
    densityExponent s j + 2 ≤ 6 * s ^ j := by
  induction j with
  | zero => simp [densityExponent]
  | succ j ih =>
    have h := Nat.mul_le_mul_right s ih
    simp only [densityExponent, pow_succ]
    nlinarith

theorem densityIter_eq_inv_pow (s j : ℕ) :
    densityIter s (1 / 16) j = ((2 : ℝ) ^ densityExponent s j)⁻¹ := by
  induction j with
  | zero => norm_num [densityIter, densityExponent]
  | succ j ih =>
    rw [densityIter, ih]
    have hdiv : ((2 : ℝ) ^ densityExponent s j)⁻¹ / 2 =
        ((2 : ℝ) ^ (densityExponent s j + 1))⁻¹ := by
      rw [pow_succ, mul_inv_rev]
      ring
    rw [hdiv, inv_pow, ← pow_mul]
    simp only [densityExponent, Nat.mul_comm]

theorem densityExponent_budget (s D j : ℕ) (hs : 2 ≤ s) (hD : 2 ≤ D)
    (hj : j < D) : densityExponent s j + 2 * s ≤ 8 * s ^ (D - 1) := by
  have ha := densityExponent_add_two_le s hs j
  have hp : s ^ j ≤ s ^ (D - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsP : s ≤ s ^ (D - 1) := by
    calc
      s = s ^ 1 := (pow_one s).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

/-- All steps have enough room to select `s` distinct coordinates. -/
theorem density_step_budget (D j : ℕ) (hD : 2 ≤ D) (hj : j < D) :
    2 * ((D + 1 : ℕ) : ℝ) ≤ densityIter (D + 1) (1 / 16) j *
      (2 : ℝ) ^ (8 * (D + 1) ^ (D - 1)) := by
  let s := D + 1
  let a := densityExponent s j
  let L := 8 * s ^ (D - 1)
  have ha : a + 2 * s ≤ L := densityExponent_budget s D j (by dsimp [s]; omega) hD hj
  have hnat : (2 * s) * 2 ^ a ≤ 2 ^ L := by
    calc
      (2 * s) * 2 ^ a ≤ 2 ^ (2 * s) * 2 ^ a :=
        Nat.mul_le_mul_right _ (show 2 * s < 2 ^ (2 * s) from Nat.lt_two_pow_self).le
      _ = 2 ^ (a + 2 * s) := by rw [← pow_add, Nat.add_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) ha
  have hreal : (2 * (s : ℝ)) * (2 : ℝ) ^ a ≤ (2 : ℝ) ^ L := by
    exact_mod_cast hnat
  have h := (le_div_iff₀ (show 0 < (2 : ℝ) ^ a by positivity)).mpr hreal
  rw [densityIter_eq_inv_pow]
  simpa only [s, a, L, div_eq_mul_inv, mul_comm] using h

/-- The quantitative complete-box lemma used by the proposed VCₙ proof. -/
theorem containsBox_of_density_one_sixteenth (D : ℕ) (hD : 2 ≤ D)
    (E : Finset (Grid D (2 ^ (8 * (D + 1) ^ (D - 1)))))
    (hE : (2 ^ (8 * (D + 1) ^ (D - 1))) ^ D ≤ 16 * E.card) :
    ContainsBox E (D + 1) := by
  apply containsBox_of_density D _ (D + 1) (by positivity) (1 / 16)
    (by norm_num) (by norm_num) E
  · have hreal : (((2 ^ (8 * (D + 1) ^ (D - 1)) : ℕ) : ℝ)) ^ D ≤
        16 * (E.card : ℝ) := by exact_mod_cast hE
    linarith
  · intro j hj
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using density_step_budget D j hD hj

end VCDimConvexBound
