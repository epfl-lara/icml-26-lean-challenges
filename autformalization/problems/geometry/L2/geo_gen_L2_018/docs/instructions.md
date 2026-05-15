# ShadowBench Instructions: `geometry/L2/geo_gen_L2_018`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
```

## Expected Declaration Names

- `affineSubspace_image_of_linear_constraints`

## Formalization Rules

```text
open Matrix

/-
Formalize in Lean the Definition (affineSubspace_image_of_linear_constraints) from Text.

The definition must be named `affineSubspace_image_of_linear_constraints`.
   Matched text (candidate 0, definition, label=affineSubspace_image_of_linear_constraints): \begin{definition}[affineSubspace_image_of_linear_constraints] \textbf{Affine set.} Show
                                                                                             that the set $\{Ax + b \mid Fx = g\}$ is affine. Here $A \in \mathbb{R}^{m \times n}$, $b
                                                                                             \in \mathbb{R}^m$, $F \in \mathbb{R}^{p \times n}$, and $g \in \mathbb{R}^p$.
                                                                                             \end{definition}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
