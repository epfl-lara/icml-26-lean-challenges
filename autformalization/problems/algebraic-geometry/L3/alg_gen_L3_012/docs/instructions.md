# ShadowBench Instructions: `algebraic-geometry/L3/alg_gen_L3_012`

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
import Mathlib
```

## Expected Declaration Names

- `functorOfPointsOver`
- `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`

## Formalization Rules

```text
open CategoryTheory
open CategoryTheory.Limits
open Opposite

/-
Formalize in Lean the following named items from Text.

1. Definition (functorOfPointsOver)
   The definition must be named `functorOfPointsOver`.
   Matched text (candidate 0, definition): \begin{definition} Let $S$ be a scheme. We say that a functor
                                           $F:(\mathrm{Sch}/S)^{\mathrm{opp}} \to \mathrm{Sets}$ is limit preserving if for every
                                           directed inverse system ${T_i}_{i \in I}$ of affine schemes with limit $T$ we have
                                           $F(T)=\mathrm{colim}_i F(T_i)$. \end{definition}
2. Theorem (locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving)
   The theorem must be named `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`.
   Matched text (candidate 1, theorem): \begin{theorem} Let $f:X \to S$ be a morphism of schemes. Then $f$ is locally of finite
                                        presentation if and only if the functor of points $h_X$ of $X$ is limit preserving.
                                        \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
