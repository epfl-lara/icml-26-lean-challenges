# ShadowBench Instructions: `algebraic-geometry/L3/alg_sche_L3_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Reflective
```

## Expected Declaration Names

- [none detected]

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
