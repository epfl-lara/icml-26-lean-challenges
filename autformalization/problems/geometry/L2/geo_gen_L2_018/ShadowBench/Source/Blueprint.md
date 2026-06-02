# Formalization Blueprint: `geometry/L2/geo_gen_L2_018`

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
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
```

## Required Names

- `affineSubspace_image_of_linear_constraints`

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
open Matrix

/-
Formalize in Lean the Theorem (affineSubspace_image_of_linear_constraints) from Text.

The Lean declaration must be named exactly:
- `affineSubspace_image_of_linear_constraints`
   Matched text (candidate 0, theorem, label=affineSubspace_image_of_linear_constraints): \begin{theorem}[affineSubspace_image_of_linear_constraints] \textbf{Affine set.} Show that
                                                                                          the set $\{Ax + b \mid Fx = g\}$ is affine. Here $A \in \mathbb{R}^{m \times n}$, $b \in
                                                                                          \mathbb{R}^m$, $F \in \mathbb{R}^{p \times n}$, and $g \in \mathbb{R}^p$. \end{theorem}
-/
```
