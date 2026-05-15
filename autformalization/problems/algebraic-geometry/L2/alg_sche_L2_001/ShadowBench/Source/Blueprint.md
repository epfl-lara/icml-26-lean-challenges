# Formalization Blueprint: `algebraic-geometry/L2/alg_sche_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.Properties
```

## Required Names

- `functionField_isFractionRing_of_affine`

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
open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

/-
Formalize in Lean the Theorem (functionField_isFractionRing_of_affine) from Text.

The theorem must be named `functionField_isFractionRing_of_affine`.
   Matched text (candidate 0, theorem, label=functionField_isFractionRing_of_affine): \begin{theorem}[functionField_isFractionRing_of_affine] Let $R$ be an integral domain. Then
                                                                                      the function field of the affine scheme $\operatorname{Spec} R$ is isomorphic to the field
                                                                                      of fractions of $R$. \end{theorem}
-/
```
