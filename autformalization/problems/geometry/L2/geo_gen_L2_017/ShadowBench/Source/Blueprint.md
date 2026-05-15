# Formalization Blueprint: `geometry/L2/geo_gen_L2_017`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
```

## Required Names

- `convex_partialSum`

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
open Set

/-
Formalize in Lean the Theorem (convex_partialSum) from Text.

The theorem must be named `convex_partialSum`.
   Matched text (candidate 0, theorem, label=convex_partialSum): \begin{theorem}[convex_partialSum] Show that if $S_1$ and $S_2$ are convex sets in
                                                                 $\mathbb{R}^{m+n}$, then so is their partial sum \[ S = \{(x, y_1 + y_2) \mid x \in
                                                                 \mathbb{R}^m, y_1, y_2 \in \mathbb{R}^n, (x, y_1) \in S_1, (x, y_2) \in S_2\}. \]
                                                                 \end{theorem}
-/
```
