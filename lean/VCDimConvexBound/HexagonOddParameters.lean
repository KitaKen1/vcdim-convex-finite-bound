import VCDimConvexBound.HexagonZeroFree
import VCDimConvexBound.PolynomialAvoidance

/-!
# Free coordinates for odd vertex configurations

Only vertices 0,1,2 in each color are free. Vertices 3,4,5 are their
negatives. Every odd configuration is recovered from these coordinates,
and every vertex coordinate is a signed variable polynomial.
-/

namespace VCDimConvexBound

abbrev HexOddVariable (r m : ℕ) := Fin r × Fin 3 × Fin m

def hexOddConfiguration {r m : ℕ} (a : HexOddVariable r m → ℝ) : HexVertex r → Point m :=
  fun v j => if h : v.2.val < 3 then a (v.1, ⟨v.2.val, h⟩, j)
    else -a (v.1, ⟨v.2.val - 3, by omega⟩, j)

def hexOddParameters {r m : ℕ} (p : HexVertex r → Point m) : HexOddVariable r m → ℝ :=
  fun a => p (a.1, Fin.castLE (by decide) a.2.1) a.2.2

theorem hexOddConfiguration_odd {r m : ℕ} (a : HexOddVariable r m → ℝ)
    (v : HexVertex r) :
    hexOddConfiguration a (hexVertexOpposite v) = -hexOddConfiguration a v := by
  rcases v with ⟨k, j⟩
  fin_cases j <;> funext l <;>
    simp [hexOddConfiguration, hexVertexOpposite, hexOpposite]

theorem continuous_hexOddConfiguration (r m : ℕ) :
    Continuous (@hexOddConfiguration r m) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro j
  dsimp only [hexOddConfiguration]
  split_ifs <;> fun_prop

theorem hexOddParameters_configuration {r m : ℕ} (a : HexOddVariable r m → ℝ) :
    hexOddParameters (hexOddConfiguration a) = a := by
  funext x
  rcases x with ⟨k, j, l⟩
  simp [hexOddParameters, hexOddConfiguration, j.isLt]

theorem hexOddConfiguration_parameters {r m : ℕ} (p : HexVertex r → Point m)
    (hp : ∀ v, p (hexVertexOpposite v) = -p v) :
    hexOddConfiguration (hexOddParameters p) = p := by
  funext v l
  rcases v with ⟨k, j⟩
  have h0 := congrFun (hp (k, 0)) l
  have h1 := congrFun (hp (k, 1)) l
  have h2 := congrFun (hp (k, 2)) l
  simp only [hexVertexOpposite, hexOpposite, Pi.neg_apply] at h0 h1 h2
  fin_cases j <;> simp [hexOddConfiguration, hexOddParameters]
  · exact h0.symm
  · exact h1.symm
  · exact h2.symm

theorem hexOddConfiguration_injective (r m : ℕ) :
    Function.Injective (@hexOddConfiguration r m) := by
  intro a b h
  simpa only [hexOddParameters_configuration] using congrArg hexOddParameters h

/-- Each actual vertex coordinate is a signed variable in the free parameters. -/
noncomputable def hexOddCoordinatePolynomial {r m : ℕ} (v : HexVertex r) (j : Fin m) :
    MvPolynomial (HexOddVariable r m) ℝ :=
  if h : v.2.val < 3 then MvPolynomial.X (v.1, ⟨v.2.val, h⟩, j)
    else -MvPolynomial.X (v.1, ⟨v.2.val - 3, by omega⟩, j)

theorem eval_hexOddCoordinatePolynomial {r m : ℕ} (a : HexOddVariable r m → ℝ)
    (v : HexVertex r) (j : Fin m) :
    MvPolynomial.eval a (hexOddCoordinatePolynomial v j) = hexOddConfiguration a v j := by
  simp only [hexOddCoordinatePolynomial, hexOddConfiguration]
  split_ifs <;> simp

theorem hexOddCoordinatePolynomial_opposite {r m : ℕ} (v : HexVertex r) (j : Fin m) :
    hexOddCoordinatePolynomial (hexVertexOpposite v) j = -hexOddCoordinatePolynomial v j := by
  apply MvPolynomial.funext
  intro a
  simp only [map_neg, eval_hexOddCoordinatePolynomial]
  exact congrFun (hexOddConfiguration_odd a v) j

/-- Any finitely many genuinely nonzero polynomial conditions can be met by a
nearby odd configuration while retaining the absence of zeros on all facets. -/
theorem exists_odd_zeroFree_polynomial_perturbation {r m : ℕ} {ι : Type*} [Fintype ι]
    (p : HexVertex r → Point m) (hp : ∀ v, p (hexVertexOpposite v) = -p v)
    (hz : HexZeroFree p) (P : ι → MvPolynomial (HexOddVariable r m) ℝ)
    (hP : ∀ i, P i ≠ 0) (U : Set (HexVertex r → Point m)) (hU : IsOpen U) (hpu : p ∈ U) :
    ∃ a : HexOddVariable r m → ℝ,
      hexOddConfiguration a ∈ U ∧ HexZeroFree (hexOddConfiguration a) ∧
        ∀ i, MvPolynomial.eval a (P i) ≠ 0 := by
  let V := hexOddConfiguration ⁻¹' (U ∩ {q | HexZeroFree q})
  have hV : IsOpen V :=
    (hU.inter (isOpen_hexZeroFree r m)).preimage (continuous_hexOddConfiguration r m)
  have hpa : hexOddParameters p ∈ V := by
    change hexOddConfiguration (hexOddParameters p) ∈ U ∩ {q | HexZeroFree q}
    rw [hexOddConfiguration_parameters p hp]
    exact ⟨hpu, hz⟩
  obtain ⟨a, ha, hne⟩ := exists_mvPolynomial_family_ne_zero_mem_open P hP V hV _ hpa
  exact ⟨a, ha.1, ha.2, hne⟩

end VCDimConvexBound
