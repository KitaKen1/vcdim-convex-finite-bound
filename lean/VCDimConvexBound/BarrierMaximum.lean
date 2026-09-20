import VCDimConvexBound.PolynomialGrowth

/-!
# Positive maxima of the barrier on closed regions

A large compact coordinate box contains the witness in its interior and
has negative barrier on its boundary. A positive maximum therefore lies
inside both the box and any closed region whose boundary is contained in
the polynomial zero set.
-/

namespace VCDimConvexBound

open scoped BigOperators Topology

variable {σ : Type*} [Fintype σ]

/-- A positive barrier value cannot occur at a zero of P. -/
theorem eval_ne_zero_of_barrier_pos (P : MvPolynomial σ ℝ) (d : ℕ)
    (ε : ℝ) (hε : 0 < ε) (x : σ → ℝ)
    (hx : 0 < MvPolynomial.eval x (polynomialBarrier P d ε)) :
    MvPolynomial.eval x P ≠ 0 := by
  intro hz
  have hs : 0 ≤ ∑ j, x j ^ (2 * d + 2) :=
    Finset.sum_nonneg fun j _ => barrierPower_nonneg d (x j)
  rw [eval_polynomialBarrier, hz] at hx
  nlinarith

/-- A positive witness in a closed region yields an unconstrained positive local maximum. -/
theorem exists_barrier_localMax_mem (P : MvPolynomial σ ℝ) (d : ℕ)
    (hP : P.totalDegree ≤ d) (ε : ℝ) (hε : 0 < ε)
    (K : Set (σ → ℝ)) (hK : IsClosed K)
    (hKlocal : ∀ x ∈ K, MvPolynomial.eval x P ≠ 0 → K ∈ 𝓝 x)
    (a : σ → ℝ) (ha : a ∈ K)
    (hapos : 0 < MvPolynomial.eval a (polynomialBarrier P d ε)) :
    ∃ b ∈ K, 0 < MvPolynomial.eval b (polynomialBarrier P d ε) ∧
      IsLocalMax (fun x => MvPolynomial.eval x (polynomialBarrier P d ε)) b := by
  classical
  let C := polynomialCoeffAbsSum P
  let S := ∑ j, |a j|
  let R := 1 + C ^ 2 / ε + S
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdiv : 0 ≤ C ^ 2 / ε := div_nonneg (sq_nonneg C) hε.le
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have hRpos : 0 < R := by linarith
  have hlarge : polynomialCoeffAbsSum P ^ 2 < ε * R ^ 2 := by
    have hcancel : ε * (C ^ 2 / ε) = C ^ 2 := by
      simpa only [mul_comm] using div_mul_cancel₀ (C ^ 2) (ne_of_gt hε)
    have hbase : C ^ 2 < ε * R := by
      dsimp [R]
      nlinarith [mul_nonneg hε.le hS]
    have hsq : R ≤ R ^ 2 := by nlinarith
    exact hbase.trans_le (mul_le_mul_of_nonneg_left hsq hε.le)
  have hain : ∀ j, |a j| < R := by
    intro j
    have hj : |a j| ≤ S := Finset.single_le_sum (f := fun i => |a i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    dsimp [R]
    linarith
  let box : Set (σ → ℝ) := Set.Icc (fun _ => -R) (fun _ => R)
  have habox : a ∈ box :=
    ⟨fun j => (abs_lt.mp (hain j)).1.le, fun j => (abs_lt.mp (hain j)).2.le⟩
  have hcompact : IsCompact (box ∩ K) := isCompact_Icc.inter_right hK
  obtain ⟨b, hb, hm⟩ := hcompact.exists_isMaxOn ⟨a, habox, ha⟩
    (MvPolynomial.continuous_eval (polynomialBarrier P d ε)).continuousOn
  have hbpos : 0 < MvPolynomial.eval b (polynomialBarrier P d ε) :=
    hapos.trans_le (hm ⟨habox, ha⟩)
  have hble : ∀ j, |b j| ≤ R := fun j => abs_le.mpr ⟨hb.1.1 j, hb.1.2 j⟩
  have hblt : ∀ j, |b j| < R := by
    intro j
    apply lt_of_le_of_ne (hble j)
    intro heq
    have hn := eval_barrier_neg_on_box_boundary P d hP ε hε R hR hlarge b hble j heq
    linarith
  have hboxnhds : box ∈ 𝓝 b := by
    have hopen : IsOpen {x : σ → ℝ | ∀ j, |x j| < R} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_lt (continuous_apply j).abs continuous_const
    apply Filter.mem_of_superset (hopen.mem_nhds hblt)
    intro x hx
    exact ⟨fun j => (abs_lt.mp (hx j)).1.le, fun j => (abs_lt.mp (hx j)).2.le⟩
  refine ⟨b, hb.2, hbpos, hm.isLocalMax ?_⟩
  exact Filter.inter_mem hboxnhds
    (hKlocal b hb.2 (eval_ne_zero_of_barrier_pos P d ε hε b hbpos))

end VCDimConvexBound
