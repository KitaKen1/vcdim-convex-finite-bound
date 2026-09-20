import VCDimConvexBound.DenseFiber

/-!
# Iterating common fibers to produce a complete box

Every coordinate of a box has the same prescribed size. The density is
updated by `δ ↦ (δ / 2)^s` at each step.
-/

namespace VCDimConvexBound

open Finset

/-- An `s × ⋯ × s` box of indices contained in `E`. -/
def ContainsBox {k m : ℕ} (E : Finset (Grid k m)) (s : ℕ) : Prop :=
  ∃ A : Fin k → Finset (Fin m), (∀ j, (A j).card = s) ∧
    ∀ i : Grid k m, (∀ j, i j ∈ A j) → i ∈ E

/-- The density after successively selecting common fibers. -/
noncomputable def densityIter (s : ℕ) (δ : ℝ) : ℕ → ℝ
  | 0 => δ
  | j + 1 => (densityIter s δ j / 2) ^ s

theorem densityIter_shift (s : ℕ) (δ : ℝ) (j : ℕ) :
    densityIter s δ (j + 1) = densityIter s ((δ / 2) ^ s) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (densityIter s δ (j + 1) / 2) ^ s =
      (densityIter s ((δ / 2) ^ s) j / 2) ^ s
    rw [ih]

/-- The first coordinate and the remaining coordinates form a product. -/
def consEquiv (k m : ℕ) : Fin m × Grid k m ≃ Grid (k + 1) m where
  toFun p := Fin.cons p.1 p.2
  invFun i := (i 0, Fin.tail i)
  left_inv p := by rcases p with ⟨a, i⟩; simp
  right_inv i := Fin.cons_self_tail i

/-- Partition the points of `E` by their remaining coordinates. -/
theorem sum_card_cons_fiber {k m : ℕ} (E : Finset (Grid (k + 1) m)) :
    ∑ b : Grid k m, (DenseFiber.fiber (fun a b => Fin.cons a b ∈ E) b).card =
      E.card := by
  classical
  have h := (consEquiv k m).sum_comp (fun i => if i ∈ E then (1 : ℕ) else 0)
  change (∑ p : Fin m × Grid k m, if Fin.cons p.1 p.2 ∈ E then (1 : ℕ) else 0) =
    ∑ i : Grid (k + 1) m, if i ∈ E then 1 else 0 at h
  rw [Fintype.sum_prod_type] at h
  calc
    _ = ∑ b : Grid k m, ∑ a : Fin m, if Fin.cons a b ∈ E then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro b _
      rw [DenseFiber.fiber, card_eq_sum_ones, sum_filter]
    _ = ∑ a : Fin m, ∑ b : Grid k m, if Fin.cons a b ∈ E then (1 : ℕ) else 0 := sum_comm
    _ = ∑ i : Grid (k + 1) m, if i ∈ E then 1 else 0 := h
    _ = _ := by simp

/-- A complete box follows whenever all intermediate densities permit another step. -/
theorem containsBox_of_density (k m s : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (E : Finset (Grid k m))
    (hdensity : δ * (m : ℝ) ^ k ≤ E.card)
    (hsteps : ∀ j < k, 2 * (s : ℝ) ≤ densityIter s δ j * m) : ContainsBox E s := by
  classical
  induction k generalizing δ with
  | zero =>
    have hpos : 0 < E.card := by
      have hreal : 0 < (E.card : ℝ) :=
        lt_of_lt_of_le hδ (by simpa only [pow_zero, mul_one] using hdensity)
      exact_mod_cast hreal
    obtain ⟨i, hi⟩ := card_pos.mp hpos
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro j _
      simpa only [Subsingleton.elim j i] using hi
  | succ k ih =>
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let R : Fin m → Grid k m → Prop := fun a b => Fin.cons a b ∈ E
    have hlarge : 2 * (s : ℝ) ≤ δ * m := hsteps 0 (Nat.zero_lt_succ k)
    have hs : s ≤ Fintype.card (Fin m) := by
      simp only [Fintype.card_fin]
      have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have hprod : δ * m ≤ (m : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ1 hmR
      have hsR : (s : ℝ) ≤ m := calc
        (s : ℝ) ≤ 2 * s := by nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
        _ ≤ δ * m := hlarge
        _ ≤ m := hprod
      exact_mod_cast hsR
    have hsum : δ * (Fintype.card (Fin m) : ℝ) * Fintype.card (Grid k m) ≤
        ∑ b : Grid k m, ((DenseFiber.fiber R b).card : ℝ) := by
      have heq := sum_card_cons_fiber E
      have heqR : (∑ b : Grid k m, ((DenseFiber.fiber R b).card : ℝ)) = E.card := by
        exact_mod_cast heq
      rw [heqR]
      simpa [card_grid, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hdensity
    obtain ⟨A, hA, hcommon⟩ := DenseFiber.exists_common_of_density R s hs δ hδ.le
      (by simpa using hlarge) hsum
    have hδ' : 0 < (δ / 2) ^ s := pow_pos (by positivity) _
    have hδ1' : (δ / 2) ^ s ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have hsteps' : ∀ j < k, 2 * (s : ℝ) ≤ densityIter s ((δ / 2) ^ s) j * m := by
      intro j hj
      rw [← densityIter_shift]
      exact hsteps (j + 1) (Nat.succ_lt_succ hj)
    obtain ⟨B, hBcard, hB⟩ := ih ((δ / 2) ^ s) hδ' hδ1' (DenseFiber.common R A)
      (by simpa using hcommon) hsteps'
    refine ⟨Fin.cons A B, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hA
      · simpa using hBcard j
    · intro i hi
      have htail : Fin.tail i ∈ DenseFiber.common R A := hB _ (fun j => by
        simpa [Fin.tail] using hi j.succ)
      have hhead : i 0 ∈ A := by simpa using hi 0
      have hrel := (DenseFiber.mem_common R A (Fin.tail i)).mp htail (i 0) hhead
      simpa only [R, Fin.cons_self_tail] using hrel

end VCDimConvexBound
