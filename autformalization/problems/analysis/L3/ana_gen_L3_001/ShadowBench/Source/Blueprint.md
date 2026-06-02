# Formalization Blueprint: `analysis/L3/ana_gen_L3_001`

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
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Real.CompleteField
```

## Required Names

- `exists_affine_between_of_concaveOn_le_convexOn`

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
open Set

/-
Formalize in Lean the Theorem (exists_affine_between_of_concaveOn_le_convexOn) from Text.

The theorem must be named `exists_affine_between_of_concaveOn_le_convexOn`.
   Matched text (candidate 0, theorem, label=exists_affine_between_of_concaveOn_le_convexOn): \begin{theorem}[exists_affine_between_of_concaveOn_le_convexOn] Suppose $f : \mathbb{R}^n
                                                                                              \to \mathbb{R}$ is convex, $g : \mathbb{R}^n \to \mathbb{R}$ is concave, $\operatorname{dom}
                                                                                              f = \operatorname{dom} g = \mathbb{R}^n$, and for all $x$, $g(x) \le f(x)$. Show that there
                                                                                              exists an affine function $h$ such that for all $x$, $g(x) \le h(x) \le f(x)$. In other
                                                                                              words, if a concave function $g$ is an underestimator of…
-/
```
