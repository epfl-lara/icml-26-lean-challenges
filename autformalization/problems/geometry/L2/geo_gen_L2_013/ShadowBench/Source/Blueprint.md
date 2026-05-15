# Formalization Blueprint: `geometry/L2/geo_gen_L2_013`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding
```

## Required Names

- `gamma_not_smooth_embedding`

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
open Manifold Set Topology

/-
Formalize in Lean the Theorem (gamma_not_smooth_embedding) from Text.

The theorem must be named `gamma_not_smooth_embedding`.
   Matched text (candidate 0, theorem, label=gamma_not_smooth_embedding): \begin{theorem}[gamma_not_smooth_embedding] Let $\gamma: \mathbb{R} \to \mathbb{R}^2$ be the
                                                                          map $\gamma(t) = (t^3, 0)$. Show that $\gamma$ is a smooth map and a topological embedding,
                                                                          but it is not a smooth embedding. \end{theorem}
-/
```
