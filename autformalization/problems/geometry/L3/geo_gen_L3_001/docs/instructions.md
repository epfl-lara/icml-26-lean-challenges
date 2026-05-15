# ShadowBench Instructions: `geometry/L3/geo_gen_L3_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
```

## Expected Declaration Names

- `morleys_trisector_theorem`

## Formalization Rules

```text
open Module

/-
Formalize in Lean the Theorem (morleys_trisector_theorem) from Text.

The theorem must be named `morleys_trisector_theorem`.
   Matched text (candidate 0, theorem, label=morleys_trisector_theorem): \begin{theorem}[morleys_trisector_theorem]\label{thm:morley_trisector} In plane geometry,
                                                                         Morley's trisector theorem states that in any triangle, the three points of intersection of
                                                                         the adjacent angle trisectors form an equilateral triangle, called the \textbf{first Morley
                                                                         triangle}. Formally, let $X, Y, Z$ be the intersections of the adjacent internal angle
                                                                         trisectors of a triangle $ABC$. Then the triangle $XYZ$ is…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
