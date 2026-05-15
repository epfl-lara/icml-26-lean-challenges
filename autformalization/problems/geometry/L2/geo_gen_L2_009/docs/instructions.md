# ShadowBench Instructions: `geometry/L2/geo_gen_L2_009`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
```

## Expected Declaration Names

- `tangentBundleProdDiffeomorph`

## Formalization Rules

```text
open scoped Manifold

/-
Formalize in Lean the Definition (tangentBundleProdDiffeomorph) from Text.

The definition must be named `tangentBundleProdDiffeomorph`.
   Matched text (candidate 0, definition, label=tangentBundleProdDiffeomorph): \begin{definition}[tangentBundleProdDiffeomorph] Prove that if $M$ and $N$ are smooth
                                                                               manifolds, then $T(M \times N)$ is diffeomorphic to $TM \times TN$. \end{definition}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
