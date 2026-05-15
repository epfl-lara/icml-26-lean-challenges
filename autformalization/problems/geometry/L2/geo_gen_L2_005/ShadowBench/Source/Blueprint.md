# Formalization Blueprint: `geometry/L2/geo_gen_L2_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
```

## Required Names

- `monges_circle_theorem`

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
