# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_001`

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
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Grp_
```

## Required Names

- `smooth_of_grpObj_of_isAlgClosed`

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
Formalize in Lean the Lemma (smooth_of_grpObj_of_isAlgClosed) from Text.

The lemma must be named `smooth_of_grpObj_of_isAlgClosed`.
   Matched text (candidate 0, theorem, label=smooth_of_grpObj_of_isAlgClosed): \begin{theorem}[smooth_of_grpObj_of_isAlgClosed] If $G$ is a group scheme over an
                                                                               algebraically closed field $k$ that is reduced and locally of finite type, then $G$ is
                                                                               smooth over $k$. \end{theorem}
-/
```
