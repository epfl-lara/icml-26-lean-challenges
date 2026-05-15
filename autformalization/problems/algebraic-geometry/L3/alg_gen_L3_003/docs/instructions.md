# ShadowBench Instructions: `algebraic-geometry/L3/alg_gen_L3_003`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
```

## Expected Declaration Names

- `locallyOfFinitePresentation_isStableUnderBaseChange`

## Formalization Rules

```text
open CategoryTheory Topology

/-
Formalize in Lean the Definition (locallyOfFinitePresentation_isStableUnderBaseChange) from Text.

The definition must be named `locallyOfFinitePresentation_isStableUnderBaseChange`.
   Matched text (candidate 0, definition, label=locallyOfFinitePresentation_isStableUnderBaseChange): \begin{definition}[locallyOfFinitePresentation_isStableUnderBaseChange] Let $f: X \to Y$ be
                                                                                                      a morphism of schemes. Assume $f$ is of finite presentation. Then the image of a locally
                                                                                                      constructible subset is locally constructible. \end{definition}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
