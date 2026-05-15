# ShadowBench Instructions: `algebraic-geometry/L2/alg_sche_L2_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.AlgebraicGeometry.Properties
```

## Expected Declaration Names

- `functionField_isFractionRing_of_affine`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
