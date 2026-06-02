# Formalization Blueprint: `geometry/L2/geo_gen_L2_016`

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
import Mathlib.Analysis.MeanInequalities
```

## Required Names

- `hyperbolic_set_convex`

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
open Finset Real

/-
Formalize in Lean the Theorem (hyperbolic_set_convex) from Text.

The theorem must be named `hyperbolic_set_convex`.
   Matched text (candidate 0, theorem, label=hyperbolic_set_convex): \begin{theorem}[hyperbolic_set_convex] Show that the hyperbolic set $S = \{x \in
                                                                     \mathbb{R}_+^n \mid \prod_{i=1}^n x_i \ge 1\}$ is convex. \textit{Hint:} If $a, b \ge 0$ and
                                                                     $0 \le \theta \le 1$, then $a^\theta b^{1-\theta} \le \theta a + (1-\theta)b$. \end{theorem}
-/
```
