# ShadowBench Instructions: `geometry/L2/geo_gen_L2_014`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
```

## Expected Declaration Names

- `d_dxtilde`

## Formalization Rules

```text
open Manifold Function

/-
Formalize in Lean the Definition (d_dxtilde) from Text.

The definition must be named `d_dxtilde`.
   Matched text (candidate 0, definition, label=d_dxtilde): \begin{definition}[d_dxtilde] Let $(x,y)$ denote the standard coordinates on $\mathbb{R}^2$.
                                                            Verify that $(\tilde{x}, \tilde{y})$ are global smooth coordinates on $\mathbb{R}^2$, where
                                                            \[ \tilde{x} = x, \quad \tilde{y} = y + x^3. \] Let $p$ be the point $(1,0) \in
                                                            \mathbb{R}^2$ (in standard coordinates), and show that \[ \frac{\partial}{\partial
                                                            x}\bigg|_p \neq \frac{\partial}{\partial \tilde{x}}\bigg|_p, \] even th…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
