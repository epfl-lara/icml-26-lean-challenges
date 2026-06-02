# ShadowBench Instructions: `geometry/L3/geo_gen_L3_003`

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
import Mathlib.Geometry.Convex.Cone.Dual
```

## Expected Declaration Names

- `dual_cone_matrix_image_nonneg`

## Formalization Rules

```text
open Matrix PointedCone

/-
Formalize in Lean the Theorem (dual_cone_matrix_image_nonneg) from Text.

The theorem must be named `dual_cone_matrix_image_nonneg`.
   Matched text (candidate 0, theorem, label=dual_cone_matrix_image_nonneg): \begin{theorem}[dual_cone_matrix_image_nonneg] Let $A \in \mathbb{R}^{m \times n}$ and
                                                                             consider the cone $K = \{Ax \mid x \succeq 0\}$. Then the dual cone of $K$ is given by \[
                                                                             K^* = \{y \in \mathbb{R}^m \mid A^T y \succeq 0\}. \] \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
