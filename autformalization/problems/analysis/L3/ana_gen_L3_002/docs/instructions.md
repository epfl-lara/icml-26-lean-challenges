# ShadowBench Instructions: `analysis/L3/ana_gen_L3_002`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
```

## Expected Declaration Names

- `open_disc_not_disjoint_union_rectangles`

## Formalization Rules

```text
open Euclidean

/-
Formalize in Lean the Theorem (open_disc_not_disjoint_union_rectangles) from Text.

The theorem must be named `open_disc_not_disjoint_union_rectangles`.
   Matched text (candidate 0, theorem, label=open_disc_not_disjoint_union_rectangles): \begin{theorem}[open_disc_not_disjoint_union_rectangles] An open disc in $\mathbb{R}^2$ is
                                                                                       not the disjoint union of open rectangles. \\ \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
