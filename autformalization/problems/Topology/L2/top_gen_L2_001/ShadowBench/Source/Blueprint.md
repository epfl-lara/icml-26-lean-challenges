# Formalization Blueprint: `Topology/L2/top_gen_L2_001`

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
import Mathlib.Order.KrullDimension
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds
```

## Required Names

- `topologicalKrullDim`
- `IsInducing.topologicalKrullDim_le`
- `IsHomeomorph.topologicalKrullDim_eq`
- `topologicalKrullDim_subspace_le`

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
open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

/-
Formalize in Lean the following named items from Text.


1. Definition (topologicalKrullDim)
   The definition must be named `topologicalKrullDim`.
   Matched text (candidate 1, paragraph): Let $T$ be a topological space. A chain of irreducible closed subsets of $T$ is a sequence
                                          $Z_0 \subset Z_1 \subset \cdots Z_n \subset T$ with $Z_i$ closed irreducible and $Z_i \ne
                                          Z_{i+1}$ for $i=0,\cdots,n-1$. The length of a chain $Z_0 \subset Z_1 \subset \cdots Z_n
                                          \subset T$ of irreducible closed subsets is the integer $n$. The Krull dimension
                                          $\text{dim}(T)$ of T is the supremum of lengths of chains of irreduc…
2. Theorem (IsInducing.topologicalKrullDim_le)
   The theorem must be named `IsInducing.topologicalKrullDim_le`.
   Matched text (candidate 3, paragraph): Theorem
3. Theorem (IsHomeomorph.topologicalKrullDim_eq)
   The theorem must be named `IsHomeomorph.topologicalKrullDim_eq`.
   Matched text (candidate 6, paragraph): If $Z_0 \subset Z_1 \subset \cdots Z_n \subset X$ is a chain of irreducible closed subsets
                                          of $X$, then $f^{-1}(Z_0) \subset f^{-1}(Z_1) \subset \cdots f^{-1}(Z_n) \subset Y$ is a
                                          chain of irreducible closed subsets of $Y$.
4. Theorem (topologicalKrullDim_subspace_le)
   The theorem must be named `topologicalKrullDim_subspace_le`.
   Matched text (candidate 11, paragraph): Theorem

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
