# Formalization Blueprint: `geometry/L2/geo_gen_L2_008`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

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
