# Formalization Blueprint: `topology/L2/top_gen_L2_010`

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
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Operator.Prod
```

## Required Names

- `Trivialization.pullback_linear`
- `VectorBundle.pullback`

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
open Bundle Set FiberBundle

/-
Formalize in Lean the following named items from Text.

1. Definition (Trivialization.pullback_linear)
   The definition must be named `Trivialization.pullback_linear`.
   Matched text (candidate 0, definition, label=Trivialization.pullback_linear): \begin{definition}[Trivialization.pullback_linear] Let $E$ be a vector bundle over a base
                                                                                 space $B$ with fiber $F$, where $F$ is a normed space over a normed field $k$. Given a
                                                                                 continuous map $f: B' \to B$, the pullback bundle $f^*E$ is defined to be a vector bundle
                                                                                 over $B'$ whose fiber $(f^*E)_x$ is defined as $E_{f(x)}$ for each $x \in B'$. It is a
                                                                                 disjoint union $\bigsqcup_{x \in B'} (f^*E)_x$ of all these fiber…
2. Theorem (VectorBundle.pullback)
   The theorem must be named `VectorBundle.pullback`.
   Matched text (candidate 1, theorem, label=VectorBundle.pullback): \begin{theorem}[VectorBundle.pullback] Given a vector bundle $E$ over a base space $B$ with
                                                                     fiber $F$ and a continuous map $f:B' \to B$, the pullback bundle $f^*E$ over $B'$ inherits
                                                                     the structure of a vector bundle. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
