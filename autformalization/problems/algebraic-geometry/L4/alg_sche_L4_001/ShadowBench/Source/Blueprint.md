# Formalization Blueprint: `algebraic-geometry/L4/alg_sche_L4_001`

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
import Aesop
```

## Required Names

- `flat_is_open`
- `flat_open_image`
- `flat_morphism_complement_of_image_is_closed`

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
Formalize in Lean the following named items from Text.

1. Theorem (flat_is_open)
   The theorem must be named `flat_is_open`.
   Matched text (candidate 0, theorem, label=flat_is_open): \begin{theorem}[flat_is_open] Let $f : X \to Y$ be a flat morphism of finite type of
                                                            Noetherian schemes. Then $f$ is an open morphism. \end{theorem}
2. Corollary (flat_open_image)
   The corollary must be named `flat_open_image`.
   Matched text (candidate 1, corollary, label=flat_open_image): \begin{corollary}[flat_open_image] Let \(f \colon X \to Y\) be a flat morphism of finite
                                                                 type of Noetherian schemes. Let \(U \subset X\) be open. Then $f(U)$ is open in $Y$.
                                                                 \end{corollary}
3. Theorem (flat_morphism_complement_of_image_is_closed)
   The theorem must be named `flat_morphism_complement_of_image_is_closed`.
   Matched text (candidate 2, theorem, label=flat_morphism_complement_of_image_is_closed): \begin{theorem}[flat_morphism_complement_of_image_is_closed] Let \(f \colon X \to Y\) be a
                                                                                           flat morphism of schemes. Let \(U \subset X\) be open, and let \(V = \operatorname{Spec} B
                                                                                           \subset Y\) be an affine open subset. Then there exists an ideal \(I \subset B\) such that
                                                                                           \[ V \setminus \bigl(f(U) \cap V\bigr) = V(I). \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
