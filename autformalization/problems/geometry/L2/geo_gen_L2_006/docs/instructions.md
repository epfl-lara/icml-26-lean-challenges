# ShadowBench Instructions: `geometry/L2/geo_gen_L2_006`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Circumcenter
```

## Expected Declaration Names

- `napoleons_theorem_inner`
- `napoleons_theorem_outer`

## Formalization Rules

```text
open Module
open scoped Real RealInnerProductSpace BigOperators

/-
Formalize in Lean the following named items from Text.

1. Theorem (napoleons_theorem_inner)
   The theorem must be named `napoleons_theorem_inner`.
   Matched text (candidate 0, theorem, label=Napoleon's Theorem (inner)): \begin{theorem}[Napoleon's Theorem (inner)]\label{thm:napoleon_inner} Let $A,B,C$ be non-
                                                                          collinear points in the plane. On each side of $\triangle ABC$, construct an equilateral
                                                                          triangle \emph{internally} (all three on the same ``inner'' side). Let $X,Y,Z$ be the
                                                                          centroids of the equilateral triangles on $AB,BC,CA$, respectively. Then $\triangle XYZ$ is
                                                                          equilateral. \end{theorem}
2. Theorem (napoleons_theorem_outer)
   The theorem must be named `napoleons_theorem_outer`.
   Matched text (candidate 1, theorem, label=napoleons_theorem_outer): \begin{theorem}[napoleons_theorem_outer]\label{thm:napoleon_outer} Let $A,B,C$ be non-
                                                                       collinear points in the plane. On each side of $\triangle ABC$, construct an equilateral
                                                                       triangle \emph{externally} (all three on the same ``outer'' side). Let $X,Y,Z$ be the
                                                                       centroids of the equilateral triangles on $AB,BC,CA$, respectively. Then $\triangle XYZ$ is
                                                                       equilateral. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
