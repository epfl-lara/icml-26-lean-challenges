# Formalization Blueprint: `geometry/L2/geo_gen_L2_010`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
```

## Required Names

- `circle_tangent_bundle_trivialization`

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
open Complex

/-
Formalize in Lean the Definition (circle_tangent_bundle_trivialization) from Text.

The definition must be named `circle_tangent_bundle_trivialization`.
   Matched text (candidate 0, definition, label=circle_tangent_bundle_trivialization): \begin{definition}[circle_tangent_bundle_trivialization] Show that $T\mathbb{S}^1$ is
                                                                                       diffeomorphic to $\mathbb{S}^1 \times \mathbb{R}$. \end{definition}
-/
```
