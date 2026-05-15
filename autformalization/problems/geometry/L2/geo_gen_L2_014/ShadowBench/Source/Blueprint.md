# Formalization Blueprint: `geometry/L2/geo_gen_L2_014`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
```

## Required Names

- `d_dxtilde`

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
open Manifold Function

/-
Formalize in Lean the Definition (d_dxtilde) from Text.

The definition must be named `d_dxtilde`.
   Matched text (candidate 0, definition, label=d_dxtilde): \begin{definition}[d_dxtilde] Let $(x,y)$ denote the standard coordinates on $\mathbb{R}^2$.
                                                            Verify that $(\tilde{x}, \tilde{y})$ are global smooth coordinates on $\mathbb{R}^2$, where
                                                            \[ \tilde{x} = x, \quad \tilde{y} = y + x^3. \] Let $p$ be the point $(1,0) \in
                                                            \mathbb{R}^2$ (in standard coordinates), and show that \[ \frac{\partial}{\partial
                                                            x}\bigg|_p \neq \frac{\partial}{\partial \tilde{x}}\bigg|_p, \] even th…
-/
```
