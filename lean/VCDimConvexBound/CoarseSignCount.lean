import VCDimConvexBound.HypersurfaceSigns
import VCDimConvexBound.SignCountConstants

/-!
# The original sign-count budget from a coarse component bound

The bound `(4 D N + 2)^(D^2 m + 2)` is enough at the original side length.
All estimates are in natural numbers. The only unproved input is the
explicit `HypersurfaceComponentBound`, rather than Warren's sharper theorem.
-/

namespace VCDimConvexBound

/-- Apply the coarse estimate to all augmented minors, including degenerate ones. -/
theorem card_minorSignPatterns_le_of_hypersurface (hM : HypersurfaceComponentBound)
    (D m : ℕ) (hD : 1 ≤ D) (hm : 0 < m) :
    (minorSignPatterns D m).card ≤
      (4 * D * (2 ^ (D + 1) * (m ^ D) ^ (D + 1)) + 2) ^ (D ^ 2 * m + 2) := by
  have h := card_ternaryPatterns_le_of_hypersurface hM D hD
    (minorPolynomial (D := D) (m := m)) totalDegree_minorPolynomial_le
  simp only [card_arrayVar] at h
  change (minorSignPatterns D m).card ≤ _ at h
  exact h.trans (by gcongr; exact card_minorIndex_le D m hm)

/-- The coarse Milnor base fits inside the same power of two as the Warren base. -/
theorem minor_hypersurface_base_le_two_pow (D L : ℕ) (hD : 1 ≤ D) (hL : 8 ≤ L) :
    4 * D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) + 2 ≤
      2 ^ (2 * L * (D + 1) ^ 2) := by
  have hpos : 0 < D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by positivity
  have hexp : 4 + 2 * D + L * D * (D + 1) ≤ 2 * L * (D + 1) ^ 2 := by
    nlinarith
  calc
    _ ≤ 8 * D * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by nlinarith
    _ ≤ 8 * (2 ^ D) * (2 ^ (D + 1) * ((2 ^ L) ^ D) ^ (D + 1)) := by
      gcongr
      exact (Nat.lt_two_pow_self (n := D)).le
    _ = 2 ^ (4 + 2 * D + L * D * (D + 1)) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

/-- The extra two variables still fit inside the existing exponent budget. -/
theorem card_minorSignPatterns_le_two_pow_of_hypersurface (hM : HypersurfaceComponentBound)
    (D L : ℕ) (hD : 1 ≤ D) (hL : 8 ≤ L) :
    (minorSignPatterns D (2 ^ L)).card ≤ 2 ^ (4 * L * (D + 1) ^ 4 * 2 ^ L) := by
  have hm : 0 < (2 : ℕ) ^ L := by positivity
  have hp : D ^ 2 * 2 ^ L + 2 ≤ 2 * (D + 1) ^ 2 * 2 ^ L := by
    calc
      _ ≤ (D ^ 2 + 2) * 2 ^ L := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith : D ^ 2 + 2 ≤ 2 * (D + 1) ^ 2)
  have he : (2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2) ≤
      4 * L * (D + 1) ^ 4 * 2 ^ L := by
    calc
      _ ≤ (2 * L * (D + 1) ^ 2) * (2 * (D + 1) ^ 2 * 2 ^ L) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ _ := card_minorSignPatterns_le_of_hypersurface hM D (2 ^ L) hD hm
    _ ≤ (2 ^ (2 * L * (D + 1) ^ 2)) ^ (D ^ 2 * 2 ^ L + 2) :=
      Nat.pow_le_pow_left (minor_hypersurface_base_le_two_pow D L hD hL) _
    _ = 2 ^ ((2 * L * (D + 1) ^ 2) * (D ^ 2 * 2 ^ L + 2)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

/-- The original explicit side length leaves strictly more than half the bit budget. -/
theorem card_minorSignPatterns_explicit_sq_lt_of_hypersurface
    (hM : HypersurfaceComponentBound) (D : ℕ) (hD : 2 ≤ D) :
    (minorSignPatterns D (2 ^ (8 * (D + 1) ^ (D - 1)))).card ^ 2 <
      2 ^ ((2 ^ (8 * (D + 1) ^ (D - 1))) ^ D) := by
  let L := 8 * (D + 1) ^ (D - 1)
  let m := 2 ^ L
  have hL : 8 ≤ L := by
    have h : 0 < (D + 1) ^ (D - 1) := by positivity
    dsimp [L]
    omega
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hb : 8 * L * (D + 1) ^ 4 < m := explicit_sign_exponent_budget D hD
  have hmD : m ^ 2 ≤ m ^ D := Nat.pow_le_pow_right hm0 hD
  have he : (4 * L * (D + 1) ^ 4 * m) * 2 < m ^ D := by
    calc
      _ = (8 * L * (D + 1) ^ 4) * m := by ring
      _ < m * m := Nat.mul_lt_mul_of_pos_right hb hm0
      _ ≤ m ^ D := by simpa [pow_two] using hmD
  have ht := card_minorSignPatterns_le_two_pow_of_hypersurface hM D L (by omega) hL
  calc
    _ ≤ (2 ^ (4 * L * (D + 1) ^ 4 * m)) ^ 2 := Nat.pow_le_pow_left ht 2
    _ = 2 ^ ((4 * L * (D + 1) ^ 4 * m) * 2) := (pow_mul _ _ _).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) he

end VCDimConvexBound
