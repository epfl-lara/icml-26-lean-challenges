# ShadowBench Instructions: `geometry/L2/geo_diff_L2_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import imports: import Mathlib.Geometry.Manifold.MFDeriv.Tangent
```

## Expected Declaration Names

- `isMIntegralCurveAt_iff'`

## Formalization Rules

```text
open scoped Manifold Topology
open Set

/-
Formalize in Lean the Lemma (isMIntegralCurveAt_iff') from Text.

The lemma must be named `isMIntegralCurveAt_iff'`.
   Matched text (candidate 0, theorem, label=isMIntegralCurveAt_iff'): \begin{theorem}[isMIntegralCurveAt_iff'] Let $M$ be a manifold and $v$ be a vector field on
                                                                       $M$. Then $\Gamma : ℝ → M$ is an integral curve of $v$ at $t_o$ if and only if there exists
                                                                       an open neighborhood $U$ of $t_o$ such that $\Gamma$ is an integral curve of $v$ on $U$.
                                                                       \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
