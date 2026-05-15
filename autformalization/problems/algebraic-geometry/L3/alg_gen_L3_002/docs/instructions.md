# ShadowBench Instructions: `algebraic-geometry/L3/alg_gen_L3_002`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
```

## Expected Declaration Names

- `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`

## Formalization Rules

```text
open CategoryTheory Limits MorphismProperty

/-
Formalize in Lean the Definition (descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact') from Text.

The definition must be named `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`.
   Matched text (candidate 0, definition, label=descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'): \begin{definition}[descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact']
                                                                                                                      Being an open immersion satisfies fpqc descent. \end{definition}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
