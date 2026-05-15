# ShadowBench Instructions: `algebra/L4/alg_geom_L4_001`

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

- `IsConstructiblePoint`
- `IsConstructibleNumber`
- `IsConstructibleAngle`
- `ConstructibleNumbers`
- `sqrt_constructible`
- `constructible_degree_power_2`
- `half_angle_constructible`
- `algebraic_of_constructible`

## Formalization Rules

```text
open Metric EuclideanSpace IntermediateField Module
open scoped PiLp Real

/-
Formalize in Lean the following named items from Text.

1. Inductive Type (IsConstructiblePoint)
   The inductive type must be named `IsConstructiblePoint`.
   Matched text (candidate 0, paragraph): Definition(`IsConstructiblePoint`)
2. Definition (IsConstructibleNumber)
   The definition must be named `IsConstructibleNumber`.
   Matched text (candidate 2, paragraph): Definition(`IsConstructibleNumber`)
3. Definition (IsConstructibleAngle)
   The definition must be named `IsConstructibleAngle`.
   Matched text (candidate 4, paragraph): Definition(`IsConstructibleAngle`)
4. Definition (ConstructibleNumbers)
   The definition must be named `ConstructibleNumbers`.
   Matched text (candidate 6, paragraph): Theorem(`ConstructibleNumbers`)
5. Lemma (sqrt_constructible)
   The lemma must be named `sqrt_constructible`.
   Matched text (candidate 12, paragraph): Theorem(`sqrt_constructible`)
6. Theorem (constructible_degree_power_2)
   The theorem must be named `constructible_degree_power_2`.
   Matched text (candidate 16, paragraph): Theorem(`constructible_degree_power_2`)
7. Theorem (half_angle_constructible)
   The theorem must be named `half_angle_constructible`.
   Matched text (candidate 21, paragraph): Theorem(`half_angle_constructible`)
8. Theorem (algebraic_of_constructible)
   The theorem must be named `algebraic_of_constructible`.
   Matched text (candidate 25, paragraph): Theorem(`algebraic_of_constructible`)

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
