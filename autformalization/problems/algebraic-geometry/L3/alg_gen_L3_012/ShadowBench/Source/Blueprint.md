# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_012`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `functorOfPointsOver`
- `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`

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
open CategoryTheory
open CategoryTheory.Limits
open Opposite

/-
Formalize in Lean the following named items from Text.

1. Definition (functorOfPointsOver)
   The definition must be named `functorOfPointsOver`.
   Matched text (candidate 0, definition): \begin{definition} Let $S$ be a scheme. We say that a functor
                                           $F:(\mathrm{Sch}/S)^{\mathrm{opp}} \to \mathrm{Sets}$ is limit preserving if for every
                                           directed inverse system ${T_i}_{i \in I}$ of affine schemes with limit $T$ we have
                                           $F(T)=\mathrm{colim}_i F(T_i)$. \end{definition}
2. Theorem (locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving)
   The theorem must be named `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`.
   Matched text (candidate 1, theorem): \begin{theorem} Let $f:X \to S$ be a morphism of schemes. Then $f$ is locally of finite
                                        presentation if and only if the functor of points $h_X$ of $X$ is limit preserving.
                                        \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
