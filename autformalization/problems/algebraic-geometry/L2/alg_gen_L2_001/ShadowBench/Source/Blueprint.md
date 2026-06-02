# Formalization Blueprint: `algebraic-geometry/L2/alg_gen_L2_001`

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
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
```

## Required Names

- `isNoetherianRing_of_away`
- `isLocallyNoetherian_of_affine_cover`

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
open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace CategoryTheory

/-
Formalize in Lean the following named items from Text.

1. Definition (isNoetherianRing_of_away)
   The definition must be named `isNoetherianRing_of_away`.
   Matched text (candidate 0, definition, label=isNoetherianRing_of_away): \begin{definition}[isNoetherianRing_of_away] A scheme $X$ is locally Noetherian if
                                                                           $\mathcal{O}_X(U)$ is Noetherian for every affine open $U$. \end{definition}
2. Theorem (isLocallyNoetherian_of_affine_cover)
   The theorem must be named `isLocallyNoetherian_of_affine_cover`.
   Matched text (candidate 1, theorem, label=isLocallyNoetherian_of_affine_cover): \begin{theorem}[isLocallyNoetherian_of_affine_cover] If a scheme $X$ has an affine open
                                                                                   covering $X = \cup_{i \in I} U_i$ such that each $\Gamma(X,U_i)$ is Noetherian, then $X$ is
                                                                                   locally Noetherian. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
