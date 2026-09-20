#!/usr/bin/env python3
"""Build the single-file proof for the current Lean4Web mathlib project."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean"
TARGET = ROOT / "lean4web" / "VCDimConvexBoundLean4Web.lean"
ENTRY = "VCDimConvexBound.FCStatement"


def module_path(name: str) -> Path:
    return SOURCE.joinpath(*name.split(".")).with_suffix(".lean")


def dependencies(name: str) -> list[str]:
    return [
        line.split()[1]
        for line in module_path(name).read_text().splitlines()
        if line.startswith("import VCDimConvexBound.")
    ]


order: list[str] = []
seen: set[str] = set()


def visit(name: str) -> None:
    if name in seen:
        return
    seen.add(name)
    for dependency in dependencies(name):
        visit(dependency)
    order.append(name)


visit(ENTRY)


def port_to_current_mathlib(source: str) -> str:
    """Apply the small API rename needed after the pinned FC/mathlib release."""
    source = re.sub(
        r"\bMvPolynomial\.monomial_mul\b",
        "MvPolynomial.monomial_mul_monomial",
        source,
    )
    source = source.replace(
        "exact Finset.prod_le_prod (fun j _ => pow_nonneg (abs_nonneg _) _)\n"
        "    (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hx j) _)",
        "exact Finset.prod_le_prod₀ (fun j _ => pow_nonneg (abs_nonneg _) _)\n"
        "    (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hx j) _)",
    )
    for old, new in {
        "if_neg": "ite_eq_right",
        "if_pos": "ite_eq_left",
        "if_false": "ite_false",
        "if_true": "ite_true",
        "dif_neg": "dite_eq_right",
        "dif_pos": "dite_eq_left",
    }.items():
        source = re.sub(rf"\b{old}\b", new, source)
    return source.replace("norm_num at * <;> decide", "norm_num at *")

preamble = r'''import Mathlib

#eval Lean.versionString

-- The monolithic file elaborates several finite case splits that are spread
-- across modules in the FC build, so it needs a larger per-command budget.
set_option maxHeartbeats 800000

/-!
# A standalone Lean4Web proof of the convex additive VC_n bound

This file is generated from the files in `../lean/VCDimConvexBound/`.
It uses mathlib only.  The definition below is the additive VC_n definition
used by the pinned Formal Conjectures target.  The repository license and
README record the source revision and attribution.
-/

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

/-- A set has additive VC_n dimension at most `d` when no additive family
indexed by `Fin n -> Fin (d + 1)` realizes every subset. -/
def HasAddVCNDimAtMost (A : Set G) (n d : ℕ) : Prop :=
  ∀ (x : Fin n → Fin (d + 1) → G) (y : Set (Fin n → Fin (d + 1)) → G),
    ¬ ∀ i s, y s + ∑ k, x k (i k) ∈ A ↔ i ∈ s
'''

parts = [preamble]
for name in order:
    body = port_to_current_mathlib("\n".join(
        line for line in module_path(name).read_text().splitlines()
        if not line.startswith("import ")
    ))
    parts.append(f"\n\n/-! ## Source module `{name}` -/\n\n{body}\n")

parts.append(r'''

namespace VCDimConvexBoundLean4Web

/-- The complete binder and conclusion of the pinned Formal Conjectures target. -/
theorem formal_conjectures_target (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, ∀ C : Set (Fin (n + 1) → ℝ), Convex ℝ C → HasAddVCNDimAtMost C n d :=
  VCDimConvexBound.fc_exists_hasAddVCNDimAtMost_n_of_convex_rn_add_one n hn

#check VCDimConvexBound.explicit_bound
#check formal_conjectures_target
#print axioms VCDimConvexBound.explicit_bound
#print axioms formal_conjectures_target

end VCDimConvexBoundLean4Web
''')

TARGET.write_text("".join(parts))
print(f"Wrote {TARGET.relative_to(ROOT)} from {len(order)} source modules")
