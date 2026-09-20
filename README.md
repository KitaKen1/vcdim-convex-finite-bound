# A Lean proof of a finite additive VC_n bound for convex sets

This repository contains a Lean proof of the uniform finite-bound target registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/b86fdb9a8f2f83d2bb2b4281586705896c0c8208/FormalConjectures/Other/VCDimConvex.lean).
For every `n ≥ 1` and every convex set `C ⊆ ℝ^(n+1)`, it proves the explicit estimate

```text
VC_n(C) ≤ 2^(8 (n + 2)^n) - 1.
```

Consequently, it proves the complete binder and conclusion of the Formal Conjectures theorem
`VCDimConvex.exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one`:

```lean
theorem vcdim_convex_uniform_bound_solved (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d
```

The witness is `d = 2^(8 * (n + 2)^n) - 1`.

**Try the standalone file in Lean4Web:**
[open the proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fvcdim-convex-finite-bound%2Frefs%2Fheads%2Fmain%2Flean4web%2FVCDimConvexBoundLean4Web.lean)

The standalone file is ported to the current Lean4Web environment used for this release:
Lean `v4.35.0-rc2` and mathlib commit
`809072a6d0abd09be38833bf6d321f9837f23892`.  It elaborates there without errors or warnings.

The upstream Formal Conjectures declaration is still marked `research open` at the pinned
revision.

## Formal Conjectures target

The `lean/` project imports both the pinned target and the proof.  Its public entry point is:

```lean
theorem VCDimConvexBoundFC.vcdim_convex_uniform_bound_solved
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ),
      Convex ℝ C → HasAddVCNDimAtMost C n d
```

The stronger explicit theorem is:

```lean
theorem VCDimConvexBound.explicit_bound
    (n : ℕ) (hn : 1 ≤ n)
    (C : Set (Fin (n + 1) → ℝ)) (hC : Convex ℝ C) :
    HasAddVCNDimAtMost C n (VCDimConvexBound.bound n)
```

Here `VCDimConvexBound.bound n` is defined as `2^(8 * (n + 2)^n) - 1`.

The Formal Conjectures project is pinned to commit
`b86fdb9a8f2f83d2bb2b4281586705896c0c8208` and Lean `v4.33.1`.  The standalone project is
separately pinned to Lean `v4.35.0-rc2`, matching the Lean4Web version current when it was
verified.  Exact dependency revisions are recorded in the two `lake-manifest.json` files.

## Mathematical Explanation (AI generated)

The proof has two main parts.

First, it proves the geometric sparsification needed for the convex-label count.  A finite
hexagon complex, mod-two boundary identities, and a general-position removal argument give the
specialized odd-map zero statement required by the Sanyal obstruction.  This produces small
representative subsets for all relevant convex-hull labels.

Second, it bounds polynomial sign patterns directly.  For polynomials `f_i`, let `P = ∏ i, f_i`
and consider

```text
G(x) = P(x)^2 - ε (1 + ∑_j x_j^(2d+2)).
```

A common positive `ε` assigns a positive local maximum of `G` to every realized strict sign
word.  At a local maximum, the derivative equations have the form

```text
x_j^(2d+1) = R_j(x),    degree R_j < 2d+1.
```

Total-degree reduction and finite-point polynomial interpolation show that such a system has at
most `(2d+1)^p` distinct solutions in `p` variables.  Hence `N` polynomials of degree at most `k`
realize at most `(2kN+1)^p` strict sign words.  Introducing one shared variable handles zero
signs and gives the ternary bound `(4kN+1)^(p+1)`.  Applied to the determinant polynomials, this
fits the numerical budget above.

No general Warren theorem, hypersurface-component theorem, Sard theorem, or nondegeneracy of
critical points is assumed by the final theorem.

## Status boundary

What this repository proves:

```text
For every n ≥ 1, there is one finite d(n) that works for every convex
C ⊆ ℝ^(n+1), with d(n) = 2^(8(n+2)^n) - 1.
```

What it does not prove:

```text
Every convex C ⊆ ℝ^3 has additive VC_2 dimension at most 2.

Every convex C ⊆ ℝ^(n+1) has additive VC_n dimension at most 3.
```

Those are separate open declarations in the same Formal Conjectures file.  The large explicit
bound proves the uniform-existence target, but does not imply either sharper bound.

## Files

| Directory | Dependency | Purpose |
|---|---|---|
| `lean/` | Formal Conjectures + Lean 4.33.1 | Source modules and the exact FC-target entry point |
| `lean4web/` | mathlib + Lean 4.35.0-rc2 | Single-file standalone version for current Lean4Web |
| `scripts/` | Python 3 | Rebuilds and applies the documented mathlib API port to the standalone file |

The standalone file is generated from the dependency closure of
`VCDimConvexBound.FCStatement`.  The generator also applies the small API renames between the
pinned Formal Conjectures mathlib and current Lean4Web mathlib; it does not change any theorem
statement or proof argument.  Regenerate it from the repository root with:

```bash
python3 scripts/build_lean4web.py
```

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both entry files contain `#print axioms` commands for the final explicit and existence theorems.
The Formal Conjectures build succeeds under Lean 4.33.1, and the standalone build succeeds
without warnings under Lean 4.35.0-rc2.  The reported dependencies in both environments are
Lean's standard foundations:

```text
[propext, Classical.choice, Quot.sound]
```

The project sources contain no `sorry`, `admit`, custom axiom, or `unsafe` theorem.

## Sources and attribution

- [Pinned Formal Conjectures target](https://github.com/google-deepmind/formal-conjectures/blob/b86fdb9a8f2f83d2bb2b4281586705896c0c8208/FormalConjectures/Other/VCDimConvex.lean)
- [Additive VC_n definition](https://github.com/google-deepmind/formal-conjectures/blob/b86fdb9a8f2f83d2bb2b4281586705896c0c8208/FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

The standalone file reproduces the relevant Formal Conjectures definition under the repository's
Apache-2.0 license and records the pinned source above.

## AI usage disclosure

This formalization and repository packaging were developed under the direction of Kenta Kitamura ([KitaKen1 on GitHub](https://github.com/KitaKen1)), with assistance from OpenAI's ChatGPT GPT-6 Astra and Codex GPT-6 Astra.
