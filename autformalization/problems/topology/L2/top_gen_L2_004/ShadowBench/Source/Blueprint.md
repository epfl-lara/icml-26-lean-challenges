# Formalization Blueprint: `topology/L2/top_gen_L2_004`

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
import Mathlib.Order.Minimal
import Mathlib.Order.Zorn
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.DiscreteSubset
```

## Required Names

- `exists_preirreducible`

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
open Set Topology

/-
Formalize in Lean the following named items from Text.

1. Theorem (exists_preirreducible)
   The theorem must be named `exists_preirreducible`.
   Matched text (candidate 1, paragraph): Let $X$ be a topological space. Let $S$ be a preirreducible subset of $X$. Then there exists
                                          a maximal preirreducible subset $T$ of $X$ containing $S$.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
