# Formalization Blueprint: `algebraic-geometry/L3/alg_sche_L3_001`

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
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Reflective
```

## Required Names

- [pending manual extraction]

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
open PrimeSpectrum
open Opposite
open CategoryTheory
open StructureSheaf
open Spec (structureSheaf)
open TopologicalSpace
open AlgebraicGeometry.LocallyRingedSpace
open TopCat.Presheaf
open TopCat.Presheaf.SheafCondition

/-
Formalize in Lean the Theorem (toΓSpec) from Text.

The theorem must be named `toΓSpec`.
   Matched text (candidate 0, theorem, label=toΓSpec): \begin{theorem}[toΓSpec] Let $X$ be a scheme. There is a canonical morphism $\varphi : X \to
                                                       \mathrm{Spec}\Gamma(X)$ from $X$ to the spectrum of its global sections where the underlying
                                                       continuous map is given by sending a point $x \in X$ to the prime ideal $p$ of global
                                                       sections that do not map to units in the stalk of the structure sheaf at $x$. \end{theorem}
-/
```
