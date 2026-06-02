# ShadowBench Instructions: `geometry/L2/geo_gen_L2_018`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
```

## Expected Declaration Names

- `affineSubspace_image_of_linear_constraints`

## Formalization Rules

```text
open Matrix

/-
Formalize in Lean the Theorem (affineSubspace_image_of_linear_constraints) from Text.

The Lean declaration must be named exactly:
- `affineSubspace_image_of_linear_constraints`
   Matched text (candidate 0, theorem, label=affineSubspace_image_of_linear_constraints): \begin{theorem}[affineSubspace_image_of_linear_constraints] \textbf{Affine set.} Show that
                                                                                          the set $\{Ax + b \mid Fx = g\}$ is affine. Here $A \in \mathbb{R}^{m \times n}$, $b \in
                                                                                          \mathbb{R}^m$, $F \in \mathbb{R}^{p \times n}$, and $g \in \mathbb{R}^p$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
