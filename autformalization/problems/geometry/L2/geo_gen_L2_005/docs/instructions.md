# ShadowBench Instructions: `geometry/L2/geo_gen_L2_005`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
```

## Expected Declaration Names

- `monges_circle_theorem`

## Formalization Rules

```text
open Module

/-
Formalize in Lean the Theorem (monges_circle_theorem) from Text.

The theorem must be named `monges_circle_theorem`.
   Matched text (candidate 0, theorem, label=monges_circle_theorem): \begin{theorem}[monges_circle_theorem]\label{thm:monge} Monge's theorem states that for any
                                                                     three circles in a plane, none of which is completely inside one of the others, the
                                                                     intersection points of each of the three pairs of external tangent lines are collinear. For
                                                                     any two circles in a plane, an external tangent is a line that is tangent to both circles
                                                                     but does not pass between them. There are two such external t…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
