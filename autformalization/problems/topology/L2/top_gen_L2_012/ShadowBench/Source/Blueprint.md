# Formalization Blueprint: `topology/L2/top_gen_L2_012`

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
import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Functors
```

## Required Names

- `skyscraperPresheaf_eq_pushforward`
- `skyscraperPresheaf_isSheaf`

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
open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Definition (skyscraperPresheaf_eq_pushforward)
   The definition must be named `skyscraperPresheaf_eq_pushforward`.
   Matched text (candidate 0, definition, label=skyscraperPresheaf_eq_pushforward): \begin{definition}[skyscraperPresheaf_eq_pushforward] Let $X$ be a topological space. $p_0
                                                                                    \in X$. Let $\mathcal{C}$ be a category with a terminal object and $A \in
                                                                                    \text{Ob}(\mathcal{C})$ be an object of $\mathcal{C}$. A skyscraper sheaf $\mathcal{F}$ with
                                                                                    value $A$ is a presheaf on $X$ with values in $\mathcal{C}$ such that $\mathcal{F}(U) = A$
                                                                                    if $p_0 \in U$ and $\mathcal{F}(U) = 1_\mathcal{C}$ if $p_0 \notin U$…
2. Theorem (skyscraperPresheaf_isSheaf)
   The theorem must be named `skyscraperPresheaf_isSheaf`.
   Matched text (candidate 1, theorem, label=skyscraperPresheaf_isSheaf): \begin{theorem}[skyscraperPresheaf_isSheaf] A skyscraper presheaf with value $A$ is a sheaf.
                                                                          \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
