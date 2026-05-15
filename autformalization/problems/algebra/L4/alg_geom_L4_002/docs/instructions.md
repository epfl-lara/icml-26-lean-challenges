# ShadowBench Instructions: `algebra/L4/alg_geom_L4_002`

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

- `cannot_double_cube`
- `cannot_square_circle`
- `cannot_trisect_60deg`

## Formalization Rules

```text
open Metric EuclideanSpace IntermediateField Module Polynomial
open scoped PiLp Real

/-
Formalize in Lean the following named items from Text.

1. Theorem (cannot_double_cube)
   The theorem must be named `cannot_double_cube`.
   Matched text (candidate 0, paragraph): Theorem(`cannot_double_cube`)
2. Theorem (cannot_square_circle)
   The theorem must be named `cannot_square_circle`.
   Matched text (candidate 4, paragraph): Theorem(`cannot_square_circle`)
3. Theorem (cannot_trisect_60deg)
   The theorem must be named `cannot_trisect_60deg`.
   Matched text (candidate 8, paragraph): Theorem(`cannot_trisect_60deg`)

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
