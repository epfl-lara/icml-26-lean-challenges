# Formalization Blueprint: `combinatorics/L3/com_gen_L3_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `LabeledTrees`
- `CayleyTreeCount`

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
open scoped Finset

/-
Formalize in Lean the following named items from Text.

1. Definition (LabeledTrees)
   The definition must be named `LabeledTrees`.
   Matched text (candidate 0, paragraph): Theorem(`CayleyTreeCount`).
2. Theorem (CayleyTreeCount)
   The theorem must be named `CayleyTreeCount`.
   Matched text (candidate 1, paragraph): There are $n^{n-2}$ distinct vertex-labeled trees with $n$ vertices.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
