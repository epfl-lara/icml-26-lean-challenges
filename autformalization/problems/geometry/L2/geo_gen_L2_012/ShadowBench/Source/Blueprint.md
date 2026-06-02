# Formalization Blueprint: `geometry/L2/geo_gen_L2_012`

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
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.NumberTheory.Real.Irrational
```

## Required Names

- `gamma_is_smooth_immersion`

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
open Complex Real Manifold

/-
Formalize in Lean the Theorem (gamma_is_smooth_immersion) from Text.

The theorem must be named `gamma_is_smooth_immersion`.
   Matched text (candidate 0, theorem, label=gamma_is_smooth_immersion): \begin{theorem}[gamma_is_smooth_immersion] Let $\mathbb{T}^2 = \mathbb{S}^1 \times
                                                                         \mathbb{S}^1 \subseteq \mathbb{C}^2$ denote the torus, and let $\alpha$ be any irrational
                                                                         number. The map $\gamma: \mathbb{R} \to \mathbb{T}^2$ given by \[ \gamma(t) = \left(e^{2\pi
                                                                         i t}, e^{2\pi i \alpha t}\right) \] is a smooth immersion. \end{theorem}
-/
```
