# Formalization Blueprint: `algebra/L4/alg_geom_L4_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `constructible_iff`
- `cyclotomic_angle_constructible_iff`

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
