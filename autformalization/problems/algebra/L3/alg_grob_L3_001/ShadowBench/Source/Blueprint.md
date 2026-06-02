# Formalization Blueprint: `algebra/L3/alg_grob_L3_001`

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
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
```

## Required Names

- `IsFinite`
- `IsProjective`
- `finite_implies_projective`

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

/-
Formalize in Lean the following named items from Text.

1. Definition (IsFinite)
   The definition must be named `IsFinite`.
   Matched text (candidate 0, theorem, label=Finite morphism): \begin{theorem}[Finite morphism] A morphism of schemes $f : X \to Y$ is called \emph{finite}
                                                               if it is affine and for every affine open subset $U = \operatorname{Spec}(A) \subset Y$, the
                                                               preimage $f^{-1}(U)$ is affine, say $f^{-1}(U) = \operatorname{Spec}(B)$, where $B$ is a
                                                               finite $A$-module. \end{theorem}
2. Definition (IsProjective)
   The definition must be named `IsProjective`.
   Matched text (candidate 1, definition, label=Projective morphism): \begin{definition}[Projective morphism] A morphism of schemes $f : X \to Y$ is called
                                                                      \emph{projective} if there exists an integer $n \ge 0$ and a closed immersion \[ i : X
                                                                      \hookrightarrow \mathbb{P}^n_Y \] such that $f$ factors as \[ X \xrightarrow{i}
                                                                      \mathbb{P}^n_Y \to Y, \] where $\mathbb{P}^n_Y$ denotes the projective $n$-space over $Y$.
                                                                      \end{definition}
3. Theorem (finite_implies_projective)
   The theorem must be named `finite_implies_projective`.
   Matched text (candidate 2, theorem, label=finite_implies_projective): \begin{theorem}[finite_implies_projective] Let $f : X \to Y$ be a finite morphism of
                                                                         schemes. Then $f$ is projective. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
