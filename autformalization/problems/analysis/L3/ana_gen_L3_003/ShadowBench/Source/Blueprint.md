# Formalization Blueprint: `analysis/L3/ana_gen_L3_003`

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
import Mathlib
```

## Required Names

- `convexOn_sq_div`

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
/-
Formalize in Lean the Theorem (convexOn_sq_div) from Text.

The theorem must be named `convexOn_sq_div`.
   Matched text (candidate 0, theorem, label=convexOn_sq_div): \begin{theorem}[convexOn_sq_div] Suppose that $f : \mathbb{R}^n \to \mathbb{R}$ is
                                                               nonnegative and convex, and $g : \mathbb{R}^n \to \mathbb{R}$ is positive and concave. Show
                                                               that the function $f^2/g$, with domain $\mathbf{dom} f \cap \mathbf{dom} g$, is convex.
                                                               \end{theorem}
-/
```
