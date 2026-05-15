# Formalization Blueprint: `geometry/L3/geo_gen_L3_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Sheaf.Basic
```

## Required Names

- `ballRnDiffeomorph`

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
open scoped Manifold
open Real

/-
Formalize in Lean the Definition (ballRnDiffeomorph) from Text.

The definition must be named `ballRnDiffeomorph`.
   Matched text (candidate 0, definition, label=ballRnDiffeomorph): \begin{definition}[ballRnDiffeomorph] \begin{enumerate} \item[(a)] Consider the maps $F:
                                                                    \mathbb{B}^n \to \mathbb{R}^n$ and $G: \mathbb{R}^n \to \mathbb{B}^n$ given by \[ F(x) =
                                                                    \frac{x}{\sqrt{1 - |x|^2}}, \qquad G(y) = \frac{y}{\sqrt{1 + |y|^2}}. \] These maps are
                                                                    smooth, and it is straightforward to compute that they are inverses of each other. Thus they
                                                                    are both diffeomorphisms, and therefore $\mathbb{B}^n$ is di…
-/
```
