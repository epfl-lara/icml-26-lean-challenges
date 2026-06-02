# Formalization Blueprint: `topology/L2/top_gen_L2_008`

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
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.CategoryTheory.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
```

## Required Names

- `paths_homotopic`
- `simply_connected_iff_paths_homotopic`

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
open CategoryTheory
open ContinuousMap
open scoped ContinuousMap

/-
Formalize in Lean the following named items from Text.

1. Definition (paths_homotopic)
   The definition must be named `paths_homotopic`.
   Matched text (candidate 0, definition, label=paths_homotopic): \begin{definition}[paths_homotopic] A topological space $X$ is simply connected if its
                                                                  fundamental groupoid is equivalent to the the groupoid with one object and the identity
                                                                  morphism. \end{definition}
2. Theorem (simply_connected_iff_paths_homotopic)
   The theorem must be named `simply_connected_iff_paths_homotopic`.
   Matched text (candidate 1, theorem, label=simply_connected_iff_paths_homotopic): \begin{theorem}[simply_connected_iff_paths_homotopic] A topological space is simply
                                                                                    connected if and only if it is path connected, and there is at most one path up to homotopy
                                                                                    between any two points. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
