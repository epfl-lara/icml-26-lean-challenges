# Formalization Blueprint: `algebraic-geometry/L4/alg_sche_L4_002`

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
import Mathlib
```

## Required Names

- `prod_projective`

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
open CategoryTheory AlgebraicGeometry

/-
Formalize in Lean the Theorem (prod_projective) from Text.

The theorem must be named `prod_projective`.
   Matched text (candidate 0, theorem, label=prod_projective): \begin{theorem}[prod_projective] Let $S$ be a scheme. The fiber product $X \times_S Y$ of
                                                               two projective $S$-schemes is again projective over $S$. \end{theorem}
-/
```
