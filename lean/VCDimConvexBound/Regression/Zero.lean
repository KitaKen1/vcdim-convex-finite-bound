import VCDimConvexBound.Basic

/-! The v2 zero-dimensional counterexample, using the actual FC definition. -/

namespace VCDimConvexBound.Regression.Zero

/-- The `n = 0` instance of the research-open lemma
`exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one`
("for every `n` there exists some `d` such that every convex set in `ℝ^{n+1}`
has VCₙ dimension at most `d`") is false: for `n = 0` no `d` works, already
for the one-point convex set `{0} ⊆ ℝ¹`.  The type `Fin 0 → Fin (d + 1)` is a
singleton, so the empty grid and the translate selector
`y s = 0` if `i₀ ∈ s`, else `1`, realize every membership pattern. -/
theorem exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one_n0_false :
    ¬ (∃ d : ℕ, ∀ C : Set (Fin (0 + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C 0 d) := by
  classical
  rintro ⟨d, hd⟩
  let C : Set (Fin 1 → ℝ) := {0}
  have hC : Convex ℝ C := convex_singleton 0
  have h := hd C hC
  unfold HasAddVCNDimAtMost at h
  let i₀ : Fin 0 → Fin (d + 1) := fun i => Fin.elim0 i
  let x : Fin 0 → Fin (d + 1) → (Fin 1 → ℝ) := fun i => Fin.elim0 i
  let y : Set (Fin 0 → Fin (d + 1)) → (Fin 1 → ℝ) :=
    fun s => if i₀ ∈ s then 0 else 1
  apply h x y
  intro i s
  have hi : i = i₀ := Subsingleton.elim _ _
  subst i
  by_cases hs : i₀ ∈ s
  · simp [C, x, y, hs]
  · have h10 : (1 : Fin 1 → ℝ) ≠ 0 := fun h10 => by simpa using congrFun h10 0
    simp [C, x, y, hs, h10]


end VCDimConvexBound.Regression.Zero
