# Formalization Blueprint: `geometry/L2/geo_gen_L2_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

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
- Skeleton candidate used: _pending_
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
Formalize in Lean the named statement from the theorem in the text.

The Lean declaration must be named exactly:
- `erdos_mordell_inequality`

Matched text (candidate 0, theorem, label=erdos_mordell_inequality):
\begin{theorem}[erdos_mordell_inequality]\label{thm:erdos_mordell}
In Euclidean geometry, the Erdős–Mordell inequality states that for any triangle $ABC$ and point $P$ inside $ABC$, the sum of the distances from $P$ to the sides is less than or equal to half of the sum of the distances from $P$ to the vertices.
Let $PL, PM, PN$ be the perpendiculars from $P$ to the sides $BC, CA, AB$ respectively. Then:
\[
PA + PB + PC \ge 2(PL + PM + PN)
\]
\end{theorem}
-/
```
