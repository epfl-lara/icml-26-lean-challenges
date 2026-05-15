# Formalization Blueprint: `algebraic-geometry/L3/alg_sche_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

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
Formalize in Lean the Definition (toΓSpec) from Text.

The definition must be named `toΓSpec`.
   Matched text (candidate 0, definition, label=toΓSpec): \begin{definition}[toΓSpec] Let $X$ be a scheme. There is a canonical morphism $\varphi : X
                                                          \to \mathrm{Spec}\Gamma(X)$ from $X$ to the spectrum of its global sections where the
                                                          underlying continuous map is given by sending a point $x \in X$ to the prime ideal $p$ of
                                                          global sections that do not map to units in the stalk of the structure sheaf at $x$.
                                                          \end{definition}
-/
```
