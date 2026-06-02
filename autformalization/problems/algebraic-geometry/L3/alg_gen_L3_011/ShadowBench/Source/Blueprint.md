# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_011`

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

- `isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal`

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
open CategoryTheory.Limits

/-
Formalize in Lean the Theorem (isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal) from Text.

The theorem must be named `isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal`.
   Matched text (candidate 0, theorem): \begin{theorem} Let $g:X \to Y$ be a morphism of schemes over $S$. If $X$ is affine over $S$
                                        and the diagonal map $\Delta:Y \to Y \times_S Y$ is affine, then $g$ is affine.
                                        \end{theorem}
-/
```
