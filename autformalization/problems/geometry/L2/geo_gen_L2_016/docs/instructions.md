# ShadowBench Instructions: `geometry/L2/geo_gen_L2_016`

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
import Mathlib.Analysis.MeanInequalities
```

## Expected Declaration Names

- `hyperbolic_set_convex`

## Formalization Rules

```text
open Finset Real

/-
Formalize in Lean the Theorem (hyperbolic_set_convex) from Text.

The theorem must be named `hyperbolic_set_convex`.
   Matched text (candidate 0, theorem, label=hyperbolic_set_convex): \begin{theorem}[hyperbolic_set_convex] Show that the hyperbolic set $S = \{x \in
                                                                     \mathbb{R}_+^n \mid \prod_{i=1}^n x_i \ge 1\}$ is convex. \textit{Hint:} If $a, b \ge 0$ and
                                                                     $0 \le \theta \le 1$, then $a^\theta b^{1-\theta} \le \theta a + (1-\theta)b$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
