# ShadowBench Instructions: `geometry/L2/geo_gen_L2_009`

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
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
```

## Expected Declaration Names

- `tangentBundleProdDiffeomorph`

## Formalization Rules

```text
open scoped Manifold ContDiff

/-
Formalize in Lean the named statement from the theorem in the text.

The Lean declaration must be named exactly:
- `tangentBundleProdDiffeomorph`

Matched text (candidate 0, theorem):
\begin{theorem}
Prove that if $M$ and $N$ are smooth manifolds, then $T(M \times N)$ is
diffeomorphic to $TM \times TN$.
\end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
