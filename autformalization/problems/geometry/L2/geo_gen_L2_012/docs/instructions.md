# ShadowBench Instructions: `geometry/L2/geo_gen_L2_012`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.NumberTheory.Real.Irrational
```

## Expected Declaration Names

- `gamma_is_smooth_immersion`

## Formalization Rules

```text
open Complex Real Manifold

/-
Formalize in Lean the Theorem (gamma_is_smooth_immersion) from Text.

The theorem must be named `gamma_is_smooth_immersion`.
   Matched text (candidate 0, theorem, label=gamma_is_smooth_immersion): \begin{theorem}[gamma_is_smooth_immersion] Let $\mathbb{T}^2 = \mathbb{S}^1 \times
                                                                         \mathbb{S}^1 \subseteq \mathbb{C}^2$ denote the torus, and let $\alpha$ be any irrational
                                                                         number. The map $\gamma: \mathbb{R} \to \mathbb{T}^2$ given by \[ \gamma(t) = \left(e^{2\pi
                                                                         i t}, e^{2\pi i \alpha t}\right) \] is a smooth immersion. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
