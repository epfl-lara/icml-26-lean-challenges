# ShadowBench Instructions: `geometry/L2/geo_gen_L2_004`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
```

## Expected Declaration Names

- `caseys_theorem`

## Formalization Rules

```text
open Module

/-
Formalize in Lean the Theorem (caseys_theorem) from Text.

The theorem must be named `caseys_theorem`.
   Matched text (candidate 0, theorem, label=caseys_theorem): \begin{theorem}[caseys_theorem]\label{thm:casey} Let $O$ be a circle of radius $R$. Let
                                                              $O_1, O_2, O_3, O_4$ be (in that order) four non-intersecting circles that lie inside $O$
                                                              and tangent to it. Denote by $t_{ij}$ the length of the exterior common bitangent of the
                                                              circles $O_i, O_j$. Then: \[ t_{12} \cdot t_{34} + t_{14} \cdot t_{23} = t_{13} \cdot
                                                              t_{24}. \] Note that in the degenerate case, where all four circle…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
