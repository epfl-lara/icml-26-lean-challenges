# Formalization Blueprint: `geometry/L3/geo_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
```

## Required Names

- `morleys_trisector_theorem`

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
Formalize in Lean the Theorem (morleys_trisector_theorem) from Text.

The theorem must be named `morleys_trisector_theorem`.
   Matched text (candidate 0, theorem, label=morleys_trisector_theorem): \begin{theorem}[morleys_trisector_theorem]\label{thm:morley_trisector} In plane geometry,
                                                                         Morley's trisector theorem states that in any triangle, the three points of intersection of
                                                                         the adjacent angle trisectors form an equilateral triangle, called the \textbf{first Morley
                                                                         triangle}. Formally, let $X, Y, Z$ be the intersections of the adjacent internal angle
                                                                         trisectors of a triangle $ABC$. Then the triangle $XYZ$ is…
-/
```
