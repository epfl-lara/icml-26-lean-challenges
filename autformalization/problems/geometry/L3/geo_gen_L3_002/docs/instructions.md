# ShadowBench Instructions: `geometry/L3/geo_gen_L3_002`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Sheaf.Basic
```

## Expected Declaration Names

- `ballRnDiffeomorph`

## Formalization Rules

```text
open scoped Manifold
open Real

/-
Formalize in Lean the Definition (ballRnDiffeomorph) from Text.

The definition must be named `ballRnDiffeomorph`.
   Matched text (candidate 0, definition, label=ballRnDiffeomorph): \begin{definition}[ballRnDiffeomorph] \begin{enumerate} \item[(a)] Consider the maps $F:
                                                                    \mathbb{B}^n \to \mathbb{R}^n$ and $G: \mathbb{R}^n \to \mathbb{B}^n$ given by \[ F(x) =
                                                                    \frac{x}{\sqrt{1 - |x|^2}}, \qquad G(y) = \frac{y}{\sqrt{1 + |y|^2}}. \] These maps are
                                                                    smooth, and it is straightforward to compute that they are inverses of each other. Thus they
                                                                    are both diffeomorphisms, and therefore $\mathbb{B}^n$ is di…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
