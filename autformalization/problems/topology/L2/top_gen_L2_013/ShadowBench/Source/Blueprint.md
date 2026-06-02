# Formalization Blueprint: `topology/L2/top_gen_L2_013`

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
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.LocallySurjective
```

## Required Names

- `IsLocallySurjective`
- `locally_surjective_iff_surjective_on_stalks`

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
open TopologicalSpace
open Opposite
open scoped AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Definition (IsLocallySurjective)
   The definition must be named `IsLocallySurjective`.
   Matched text (candidate 0, theorem): \begin{theorem} A map of presheaves \( T : \mathcal{F} \to \mathcal{G} \) is \emph{locally
                                        surjective} if for every open set \( U \), every section \( t \in \mathcal{G}(U) \), and
                                        every point \( x \in U \), there exists an open set \( V \) such that \( x \in V \subseteq U
                                        \) and a section \( s \in \mathcal{F}(V) \) such that \( T(s) = t|_V \). \end{theorem}
2. Theorem (locally_surjective_iff_surjective_on_stalks)
   The theorem must be named `locally_surjective_iff_surjective_on_stalks`.
   Matched text (candidate 1, theorem, label=locally_surjective_iff_surjective_on_stalks): \begin{theorem}[locally_surjective_iff_surjective_on_stalks] A morphism \( T : \mathcal{F}
                                                                                           \to \mathcal{G} \) of presheaves is locally surjective if and only if for every point \( x
                                                                                           \in X \), the induced map on stalks \( \mathcal{F}_x \to \mathcal{G}_x \) is surjective.
                                                                                           \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
