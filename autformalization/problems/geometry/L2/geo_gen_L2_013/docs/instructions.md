# ShadowBench Instructions: `geometry/L2/geo_gen_L2_013`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding
```

## Expected Declaration Names

- `gamma_not_smooth_embedding`

## Formalization Rules

```text
open Manifold Set Topology

/-
Formalize in Lean the Theorem (gamma_not_smooth_embedding) from Text.

The theorem must be named `gamma_not_smooth_embedding`.
   Matched text (candidate 0, theorem, label=gamma_not_smooth_embedding): \begin{theorem}[gamma_not_smooth_embedding] Let $\gamma: \mathbb{R} \to \mathbb{R}^2$ be the
                                                                          map $\gamma(t) = (t^3, 0)$. Show that $\gamma$ is a smooth map and a topological embedding,
                                                                          but it is not a smooth embedding. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
