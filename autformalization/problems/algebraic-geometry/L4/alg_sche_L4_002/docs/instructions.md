# ShadowBench Instructions: `algebraic-geometry/L4/alg_sche_L4_002`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib
```

## Expected Declaration Names

- `prod_projective`

## Formalization Rules

```text
open CategoryTheory AlgebraicGeometry

/-
Formalize in Lean the Theorem (prod_projective) from Text.

The theorem must be named `prod_projective`.
   Matched text (candidate 0, theorem, label=prod_projective): \begin{theorem}[prod_projective] Let $S$ be a scheme. The fiber product $X \times_S Y$ of
                                                               two projective $S$-schemes is again projective over $S$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
