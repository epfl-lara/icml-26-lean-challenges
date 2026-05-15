# Formalization Blueprint: `geometry/L2/geo_gen_L2_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Geometry.Euclidean.Projection
```

## Required Names

- `erdos_mordell_inequality`

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
open Affine

/-
Formalize in Lean the Theorem (erdos_mordell_inequality) from Text.

The theorem must be named `erdos_mordell_inequality`.
   Matched text (candidate 0, theorem, label=erdos_mordell_inequality): \begin{theorem}[erdos_mordell_inequality]\label{thm:erdos_mordell} In Euclidean geometry,
                                                                        the Erdős–Mordell inequality states that for any triangle $ABC$ and point $P$ inside $ABC$,
                                                                        the sum of the distances from $P$ to the sides is less than or equal to half of the sum of
                                                                        the distances from $P$ to the vertices. Let $PL, PM, PN$ be the perpendiculars from $P$ to
                                                                        the sides $BC, CA, AB$ respectively. Then: \[ PA + PB +…
-/
```
