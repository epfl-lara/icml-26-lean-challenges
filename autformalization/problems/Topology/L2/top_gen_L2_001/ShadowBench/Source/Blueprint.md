# Formalization Blueprint: `Topology/L2/top_gen_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

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
- `ABM_Topology_L2_top_gen_L2_001_item_5`
- `ABM_Topology_L2_top_gen_L2_001_item_6`
- `ABM_Topology_L2_top_gen_L2_001_item_7`
- `ABM_Topology_L2_top_gen_L2_001_item_8`
- `ABM_Topology_L2_top_gen_L2_001_item_9`
- `ABM_Topology_L2_top_gen_L2_001_item_10`
- `ABM_Topology_L2_top_gen_L2_001_item_11`
- `ABM_Topology_L2_top_gen_L2_001_item_12`
- `ABM_Topology_L2_top_gen_L2_001_item_13`
- `ABM_Topology_L2_top_gen_L2_001_item_14`
- `ABM_Topology_L2_top_gen_L2_001_item_15`

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
open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

/-
Formalize in Lean the following named items from Text.

1. Definition (topologicalKrullDim)
   The definition must be named `topologicalKrullDim`.
   Matched text (candidate 0, paragraph): Definition
2. Theorem (IsInducing.topologicalKrullDim_le)
   The theorem must be named `IsInducing.topologicalKrullDim_le`.
   Matched text (candidate 1, paragraph): Let $T$ be a topological space. A chain of irreducible closed subsets of $T$ is a sequence
                                          $Z_0 \subset Z_1 \subset \cdots Z_n \subset T$ with $Z_i$ closed irreducible and $Z_i \ne
                                          Z_{i+1}$ for $i=0,\cdots,n-1$. The length of a chain $Z_0 \subset Z_1 \subset \cdots Z_n
                                          \subset T$ of irreducible closed subsets is the integer $n$. The Krull dimension
                                          $\text{dim}(T)$ of T is the supremum of lengths of chains of irreduc…
3. Theorem (IsHomeomorph.topologicalKrullDim_eq)
   The theorem must be named `IsHomeomorph.topologicalKrullDim_eq`.
   Matched text (candidate 2, paragraph): Let $X$, $Y$ be topological spaces.
4. Theorem (topologicalKrullDim_subspace_le)
   The theorem must be named `topologicalKrullDim_subspace_le`.
   Matched text (candidate 3, paragraph): Theorem
5. Theorem (ABM_Topology_L2_top_gen_L2_001_item_5)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_5`.
   Matched text (candidate 4, paragraph): If $f: Y \to X$ is inducing, then $\text{dim}(Y) \le \text{dim}(X)$.
6. Theorem (ABM_Topology_L2_top_gen_L2_001_item_6)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_6`.
   Matched text (candidate 5, paragraph): proof
7. Theorem (ABM_Topology_L2_top_gen_L2_001_item_7)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_7`.
   Matched text (candidate 6, paragraph): If $Z_0 \subset Z_1 \subset \cdots Z_n \subset X$ is a chain of irreducible closed subsets
                                          of $X$, then $f^{-1}(Z_0) \subset f^{-1}(Z_1) \subset \cdots f^{-1}(Z_n) \subset Y$ is a
                                          chain of irreducible closed subsets of $Y$.
8. Theorem (ABM_Topology_L2_top_gen_L2_001_item_8)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_8`.
   Matched text (candidate 7, paragraph): Theorem
9. Theorem (ABM_Topology_L2_top_gen_L2_001_item_9)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_9`.
   Matched text (candidate 8, paragraph): The topological Krull dimension is invariant under homeomorphisms.
10. Theorem (ABM_Topology_L2_top_gen_L2_001_item_10)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_10`.
   Matched text (candidate 9, paragraph): Proof
11. Theorem (ABM_Topology_L2_top_gen_L2_001_item_11)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_11`.
   Matched text (candidate 10, paragraph): Let $f:X \to Y$ be a homeomorphism with its inverse $f^{-1}:Y \to X$. Then both $f$ and
                                           $f^{-1}$ are inducing, so we have $\text{dim}(X) \le \text{dim}(Y)$ and $\text{dim}(Y) \le
                                           \text{dim}(X)$. It follows that $\text{dim}(X) = \text{dim}(Y)$.
12. Theorem (ABM_Topology_L2_top_gen_L2_001_item_12)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_12`.
   Matched text (candidate 11, paragraph): Theorem
13. Theorem (ABM_Topology_L2_top_gen_L2_001_item_13)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_13`.
   Matched text (candidate 12, paragraph): For any subspace $Y \subseteq X$, we have $\text{dim}(Y) \le \text{dim}(X)$.
14. Theorem (ABM_Topology_L2_top_gen_L2_001_item_14)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_14`.
   Matched text (candidate 13, paragraph): Proof
15. Theorem (ABM_Topology_L2_top_gen_L2_001_item_15)
   The theorem must be named `ABM_Topology_L2_top_gen_L2_001_item_15`.
   Matched text (candidate 14, paragraph): Since any embedding $Y \to X$ is inducing, we have $\text{dim}(Y) \le \text{dim}(X)$.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
