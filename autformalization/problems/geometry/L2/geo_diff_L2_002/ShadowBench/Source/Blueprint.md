# Formalization Blueprint: `geometry/L2/geo_diff_L2_002`

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
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
```

## Required Names

- `isMIntegralCurveAt_iff'`

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
open scoped Manifold Topology
open Set

/-
Formalize in Lean the Lemma (isMIntegralCurveAt_iff') from Text.

The lemma must be named `isMIntegralCurveAt_iff'`.
   Matched text (candidate 0, theorem, label=isMIntegralCurveAt_iff'): \begin{theorem}[isMIntegralCurveAt_iff'] Let $M$ be a manifold and $v$ be a vector field on
                                                                       $M$. Then $\Gamma : ℝ → M$ is an integral curve of $v$ at $t_o$ if and only if there exists
                                                                       an open neighborhood $U$ of $t_o$ such that $\Gamma$ is an integral curve of $v$ on $U$.
                                                                       \end{theorem}
-/
```
