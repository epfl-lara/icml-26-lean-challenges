# ShadowBench Instructions: `algebra/L4/alg_geom_L4_003`

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

- `constructible_iff`
- `cyclotomic_angle_constructible_iff`

## Formalization Rules

```text
open Metric EuclideanSpace IntermediateField Module Polynomial
open scoped PiLp Real

/-
Formalize in Lean the following named items from Text.

1. Theorem (constructible_iff)
   The theorem must be named `constructible_iff`.
   Matched text (candidate 0, paragraph): Theorem(`constructible_iff`)
2. Theorem (cyclotomic_angle_constructible_iff)
   The theorem must be named `cyclotomic_angle_constructible_iff`.
   Matched text (candidate 5, paragraph): Theorem(`cyclotomic_angle_constructible_iff`)

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
