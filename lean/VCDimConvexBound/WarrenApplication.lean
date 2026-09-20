import VCDimConvexBound.SignPatterns

/-!
# Applying a strict Warren bound to arbitrary finite polynomial families

Warren's estimate remains an explicit hypothesis. The results here supply the
finite reindexing and the passage from ternary signs to strict signs, including
the extra variable and doubled family. They do not prove Warren's theorem.
-/

namespace VCDimConvexBound

theorem strictPatterns_comp_domain {ι α β : Type*} [Fintype ι]
    (f : ι → α → ℝ) (u : β → α) (hu : Function.Surjective u) :
    strictPatterns (fun i x => f i (u x)) = strictPatterns f := by
  classical
  ext s
  simp only [strictPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨u x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hu x
    exact ⟨y, hx⟩

theorem card_strictPatterns_reindex {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (f : ι → α → ℝ) :
    (strictPatterns (fun i => f (e i))).card = (strictPatterns f).card := by
  classical
  apply Finset.card_bij (fun s _ i => s (e.symm i))
  · intro s hs
    obtain ⟨x, hx⟩ : ∃ x, ∀ i, if s i then 0 < f (e i) x else f (e i) x < 0 := by
      simpa [strictPatterns] using hs
    simp only [strictPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, fun i => by simpa using hx (e.symm i)⟩
  · intro s _ t _ h
    funext i
    simpa using congrFun h (e i)
  · intro s hs
    obtain ⟨x, hx⟩ : ∃ x, ∀ i, if s i then 0 < f i x else f i x < 0 := by
      simpa [strictPatterns] using hs
    refine ⟨fun i => s (e i), ?_, ?_⟩
    · simp only [strictPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, fun i => hx (e i)⟩
    · funext i
      simp

/-- Reindex the finite variable and polynomial types to the `Fin` form of Warren. -/
theorem card_strictPatterns_le_of_warren {ι σ : Type*} [Fintype ι] [Fintype σ]
    (hW : WarrenStrictBound) (k : ℕ) (hp : 0 < Fintype.card σ) (hk : 0 < k)
    (hN : Fintype.card σ ≤ Fintype.card ι) (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ k) :
    ((strictPatterns (fun i x => MvPolynomial.eval x (f i))).card : ℝ) ≤
      (4 * Real.exp 1 * k * Fintype.card ι / Fintype.card σ) ^ Fintype.card σ := by
  classical
  let eι := (Fintype.equivFin ι).symm
  let eσ := Fintype.equivFin σ
  let g := fun i : Fin (Fintype.card ι) => MvPolynomial.rename eσ (f (eι i))
  have hu : Function.Surjective (fun x : Fin (Fintype.card σ) → ℝ => x ∘ eσ) := by
    intro x
    refine ⟨x ∘ eσ.symm, ?_⟩
    funext i
    simp
  have hc : (strictPatterns (fun i x => MvPolynomial.eval x (g i))).card =
      (strictPatterns (fun i x => MvPolynomial.eval x (f i))).card := by
    calc
      _ = (strictPatterns (fun i x => MvPolynomial.eval x (f (eι i)))).card := by
        simpa only [g, MvPolynomial.eval_rename] using congrArg Finset.card
          (strictPatterns_comp_domain (fun i x => MvPolynomial.eval x (f (eι i)))
            (fun x : Fin (Fintype.card σ) → ℝ => x ∘ eσ) hu)
      _ = _ := card_strictPatterns_reindex eι (fun i x => MvPolynomial.eval x (f i))
  rw [← hc]
  exact hW _ _ k hp hk hN g
    (fun i => (MvPolynomial.totalDegree_rename_le eσ _).trans (hf (eι i)))

/-- The strict polynomial perturbations realize exactly the strict function perturbations. -/
theorem card_strictPatterns_perturbPolynomials {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℝ) :
    (strictPatterns (fun j x => MvPolynomial.eval x (perturbPolynomials f j))).card =
      (strictPatterns (perturbFunctions (fun i x => MvPolynomial.eval x (f i)))).card := by
  classical
  let u : ((σ → ℝ) × ℝ) → (Option σ → ℝ) := fun x o => o.elim x.2 x.1
  have hu : Function.Surjective u := by
    intro x
    refine ⟨(fun i => x (some i), x none), ?_⟩
    funext o
    cases o <;> rfl
  have he : (fun j x => MvPolynomial.eval (u x) (perturbPolynomials f j)) =
      perturbFunctions (fun i x => MvPolynomial.eval x (f i)) := by
    funext j x
    exact eval_perturbPolynomials f x.1 x.2 j
  have h := strictPatterns_comp_domain
    (fun j x => MvPolynomial.eval x (perturbPolynomials f j)) u hu
  rw [he] at h
  exact (congrArg Finset.card h).symm

/-- The complete ternary sign estimate, conditional only on the stated Warren input. -/
theorem card_ternaryPatterns_le_of_warren {ι σ : Type*} [Fintype ι] [Fintype σ]
    (hW : WarrenStrictBound) (k : ℕ) (hk : 0 < k)
    (hN : Fintype.card σ + 1 ≤ 2 * Fintype.card ι)
    (f : ι → MvPolynomial σ ℝ) (hf : ∀ i, (f i).totalDegree ≤ k) :
    ((ternaryPatterns (fun i x => MvPolynomial.eval x (f i))).card : ℝ) ≤
      (8 * Real.exp 1 * k * Fintype.card ι / (Fintype.card σ + 1)) ^
        (Fintype.card σ + 1) := by
  classical
  have h := card_strictPatterns_le_of_warren hW k
    (by simp : 0 < Fintype.card (Option σ)) hk
    (by simpa [Nat.mul_comm] using hN : Fintype.card (Option σ) ≤ Fintype.card (ι × Bool))
    (perturbPolynomials f) (totalDegree_perturbPolynomials_le f k hk hf)
  have hc := card_ternaryPatterns_le_strictPatterns_perturb
    (fun i x => MvPolynomial.eval x (f i))
  rw [← card_strictPatterns_perturbPolynomials f] at hc
  refine (Nat.cast_le.mpr hc).trans (h.trans_eq ?_)
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

end VCDimConvexBound
