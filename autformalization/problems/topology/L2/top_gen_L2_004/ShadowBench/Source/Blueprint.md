# Formalization Blueprint: `topology/L2/top_gen_L2_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Order.Minimal
import Mathlib.Order.Zorn
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.DiscreteSubset
```

## Required Names

- `isIrreducible_singleton`
- `isPreirreducible_iff_closure`
- `isIrreducible_iff_closure`
- `exists_preirreducible`

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
open Set Topology

/-
Formalize in Lean the following named items from Text.

1. Theorem (isIrreducible_singleton)
   The theorem must be named `isIrreducible_singleton`.
   Matched text (candidate 0, paragraph): Theorem
2. Theorem (isPreirreducible_iff_closure)
   The theorem must be named `isPreirreducible_iff_closure`.
   Matched text (candidate 1, paragraph): Let $X$ be a topological space. Let $S$ be a preirreducible subset of $X$. Then there exists
                                          a maximal preirreducible subset $T$ of $X$ containing $S$.
3. Theorem (isIrreducible_iff_closure)
   The theorem must be named `isIrreducible_iff_closure`.
   Matched text (candidate 2, paragraph): Proof
4. Theorem (exists_preirreducible)
   The theorem must be named `exists_preirreducible`.
   Matched text (candidate 3, paragraph): We use Zorn's Lemma. Consider the set $\mathcal{S} = \{T \subseteq X | T \text{ is
                                          preirreducible and } S \subseteq T\}$. It is nonempty since $S \in \mathcal{S}$. If
                                          $\mathcal{C}$ is a chain of $\mathcal{S}$, we claim that $C_0:=\cup_{C \in \mathcal{C}} C$
                                          is the upper bound of the chain $\mathcal{C}$. It suffices to show that $C_0$ is
                                          preirreducible. Suppose $U,V$ are open subsets of $X$ such that $C_0 \cap U \ne…

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
