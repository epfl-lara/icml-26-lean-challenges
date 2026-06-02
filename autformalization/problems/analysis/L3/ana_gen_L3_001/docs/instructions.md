# ShadowBench Instructions: `analysis/L3/ana_gen_L3_001`

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
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Real.CompleteField
```

## Expected Declaration Names

- `exists_affine_between_of_concaveOn_le_convexOn`

## Formalization Rules

```text
open Set

/-
Formalize in Lean the Theorem (exists_affine_between_of_concaveOn_le_convexOn) from Text.

The theorem must be named `exists_affine_between_of_concaveOn_le_convexOn`.
   Matched text (candidate 0, theorem, label=exists_affine_between_of_concaveOn_le_convexOn): \begin{theorem}[exists_affine_between_of_concaveOn_le_convexOn] Suppose $f : \mathbb{R}^n
                                                                                              \to \mathbb{R}$ is convex, $g : \mathbb{R}^n \to \mathbb{R}$ is concave, $\operatorname{dom}
                                                                                              f = \operatorname{dom} g = \mathbb{R}^n$, and for all $x$, $g(x) \le f(x)$. Show that there
                                                                                              exists an affine function $h$ such that for all $x$, $g(x) \le h(x) \le f(x)$. In other
                                                                                              words, if a concave function $g$ is an underestimator of…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
