# Formalization Blueprint: `topology/L2/top_gen_L2_005`

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
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton
```

## Required Names

- `setoid`

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
open scoped unitInterval Topology
open Homeomorph

/-
Formalize in Lean the Definition (setoid) from Text.

The definition must be named `setoid`.
   Matched text (candidate 0, definition, label=setoid): \begin{definition}[setoid] Let $X$ be a topological space, $x \in X$ and $\Omega^{N}(X,x)$
                                                         denote the space of \emph{generalized $N$-loops in $X$ based at $x$} i.e. \[ \Omega^{N}(X,x)
                                                         := \Bigl\{\, f : I^{N} \to X \ \text{continuous} \ \Bigm|\ f(y)=x \text{ for all } y \in
                                                         \partial I^{N} \Bigr\} \] With respect to the usual topology on $ \Omega^{N}(X,x)$ inherited
                                                         from the compact-open topology on continuous maps, th…
-/
```
