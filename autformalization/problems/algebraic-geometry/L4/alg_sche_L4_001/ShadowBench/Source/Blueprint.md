# Formalization Blueprint: `algebraic-geometry/L4/alg_sche_L4_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `flat_is_open`
- `ABM_algebraic_geometry_L4_alg_sche_L4_001_item_2`
- `ABM_algebraic_geometry_L4_alg_sche_L4_001_item_3`

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
open CategoryTheory AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Theorem (flat_is_open)
   The theorem must be named `flat_is_open`.
   Matched text (candidate 0, theorem, label=flat_is_open): \begin{theorem}[flat_is_open] Let $f : X \to Y$ be a flat morphism of finite type of
                                                            Noetherian schemes. Then $f$ is an open morphism. \end{theorem}
2. Corollary (ABM_algebraic_geometry_L4_alg_sche_L4_001_item_2)
   The corollary must be named `ABM_algebraic_geometry_L4_alg_sche_L4_001_item_2`.
   Matched text (candidate 1, corollary): \begin{corollary} Let \(f \colon X \to Y\) be a flat morphism of finite type of Noetherian
                                          schemes. Let \(U \subset X\) be open. Then $f(U)$ is open in $Y$. \end{corollary}
3. Theorem (ABM_algebraic_geometry_L4_alg_sche_L4_001_item_3)
   The theorem must be named `ABM_algebraic_geometry_L4_alg_sche_L4_001_item_3`.
   Matched text (candidate 2, theorem): \begin{theorem} Let \(f \colon X \to Y\) be a flat morphism of schemes. Let \(U \subset X\)
                                        be open, and let \(V = \operatorname{Spec} B \subset Y\) be an affine open subset. Then
                                        there exists an ideal \(I \subset B\) such that \[ V \setminus \bigl(f(U) \cap V\bigr) =
                                        V(I). \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
