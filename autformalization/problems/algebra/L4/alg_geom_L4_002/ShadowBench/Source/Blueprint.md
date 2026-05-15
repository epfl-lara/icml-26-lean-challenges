# Formalization Blueprint: `algebra/L4/alg_geom_L4_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `cannot_double_cube`
- `cannot_square_circle`
- `cannot_trisect_60deg`

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
