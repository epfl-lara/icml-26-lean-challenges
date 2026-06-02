# Formalization Blueprint: `geometry/L2/geo_gen_L2_014`

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
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
```

## Required Names

- `partial_x_ne_partial_xtilde_at_p`

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
open Manifold Function

/-
Formalize in Lean the Theorem (partial_x_ne_partial_xtilde_at_p) from Text.

The theorem must be named `partial_x_ne_partial_xtilde_at_p`.
   Matched text (candidate 0, theorem, label=partial_x_ne_partial_xtilde_at_p): \begin{theorem}[partial_x_ne_partial_xtilde_at_p] Let $(x,y)$ denote the standard
                                                                                coordinates on $\mathbb{R}^2$. Verify that $(\tilde{x}, \tilde{y})$ are global smooth
                                                                                coordinates on $\mathbb{R}^2$, where \[ \tilde{x} = x, \quad \tilde{y} = y + x^3. \] Let $p$
                                                                                be the point $(1,0) \in \mathbb{R}^2$ (in standard coordinates), and show that \[
                                                                                \frac{\partial}{\partial x}\bigg|_p \neq \frac{\partial}{\partial \tilde{x}}…
-/
```
