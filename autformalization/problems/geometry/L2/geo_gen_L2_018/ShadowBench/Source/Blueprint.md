# Formalization Blueprint: `geometry/L2/geo_gen_L2_018`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
```

## Required Names

- `affineSubspace_image_of_linear_constraints`

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
open Matrix

/-
Formalize in Lean the Definition (affineSubspace_image_of_linear_constraints) from Text.

The definition must be named `affineSubspace_image_of_linear_constraints`.
   Matched text (candidate 0, definition, label=affineSubspace_image_of_linear_constraints): \begin{definition}[affineSubspace_image_of_linear_constraints] \textbf{Affine set.} Show
                                                                                             that the set $\{Ax + b \mid Fx = g\}$ is affine. Here $A \in \mathbb{R}^{m \times n}$, $b
                                                                                             \in \mathbb{R}^m$, $F \in \mathbb{R}^{p \times n}$, and $g \in \mathbb{R}^p$.
                                                                                             \end{definition}
-/
```
