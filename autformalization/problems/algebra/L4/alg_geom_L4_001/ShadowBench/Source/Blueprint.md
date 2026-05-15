# Formalization Blueprint: `algebra/L4/alg_geom_L4_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `IsConstructiblePoint`
- `IsConstructibleNumber`
- `IsConstructibleAngle`
- `ConstructibleNumbers`
- `sqrt_constructible`
- `constructible_degree_power_2`
- `half_angle_constructible`
- `algebraic_of_constructible`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

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
