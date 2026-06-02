# ShadowBench Instructions: `algebraic-geometry/L2/alg_gen_L2_001`

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
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
```

## Expected Declaration Names

- `isNoetherianRing_of_away`
- `isLocallyNoetherian_of_affine_cover`

## Formalization Rules

```text
open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace CategoryTheory

/-
Formalize in Lean the following named items from Text.

1. Definition (isNoetherianRing_of_away)
   The definition must be named `isNoetherianRing_of_away`.
   Matched text (candidate 0, definition, label=isNoetherianRing_of_away): \begin{definition}[isNoetherianRing_of_away] A scheme $X$ is locally Noetherian if
                                                                           $\mathcal{O}_X(U)$ is Noetherian for every affine open $U$. \end{definition}
2. Theorem (isLocallyNoetherian_of_affine_cover)
   The theorem must be named `isLocallyNoetherian_of_affine_cover`.
   Matched text (candidate 1, theorem, label=isLocallyNoetherian_of_affine_cover): \begin{theorem}[isLocallyNoetherian_of_affine_cover] If a scheme $X$ has an affine open
                                                                                   covering $X = \cup_{i \in I} U_i$ such that each $\Gamma(X,U_i)$ is Noetherian, then $X$ is
                                                                                   locally Noetherian. \end{theorem}

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
