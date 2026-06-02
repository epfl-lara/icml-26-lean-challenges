# Formalization Blueprint: `geometry/L2/geo_gen_L2_008`

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
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Defs
```

## Required Names

- `smooth_function_separating_closed_sets`

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
open scoped ContDiff Manifold

/-
Formalize in Lean the Theorem (smooth_function_separating_closed_sets) from Text.

The theorem must be named `smooth_function_separating_closed_sets`.
   Matched text (candidate 0, theorem, label=smooth_function_separating_closed_sets): \begin{theorem}[smooth_function_separating_closed_sets] Suppose $A$ and $B$ are disjoint
                                                                                      closed subsets of a smooth manifold $M$. Show that there exists $f \in C^\infty(M)$ such
                                                                                      that $0 \le f(x) \le 1$ for all $x \in M$, $f^{-1}(0) = A$, and $f^{-1}(1) = B$.
                                                                                      \end{theorem}
-/
```
