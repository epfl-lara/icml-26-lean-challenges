# Formalization Blueprint: `geometry/L2/geo_gen_L2_021`

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

- `global_integralCurve_unique_fundamental_period`

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
open scoped Manifold ContDiff

/-
Formalize in Lean the Theorem (global_integralCurve_unique_fundamental_period) from Text.

The theorem must be named `global_integralCurve_unique_fundamental_period`.
   Matched text (candidate 0, theorem, label=global_integralCurve_unique_fundamental_period): \begin{theorem}[global_integralCurve_unique_fundamental_period] Suppose $M$ is a smooth
                                                                                              manifold, $X \in \mathfrak{X}(M)$, and $\gamma: \mathbb{R} \to M$ is a global integral curve
                                                                                              of $X$. We say $\gamma$ is \textbf{periodic} if there is a number $T > 0$ such that
                                                                                              $\gamma(t + T) = \gamma(t)$ for all $t \in \mathbb{R}$. Show that if $\gamma$ is periodic
                                                                                              and nonconstant, then there exists a unique positive number $T$…
-/
```
