# ShadowBench Instructions: `analysis/L3/ana_gen_L3_005`

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
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
```

## Expected Declaration Names

- `integral_cos_sq_tendsto_half_measure`

## Formalization Rules

```text
open MeasureTheory Real Complex Set NNReal Filter Topology

/-
Formalize in Lean the Theorem (integral_cos_sq_tendsto_half_measure) from Text.

The theorem must be named `integral_cos_sq_tendsto_half_measure`.
   Matched text (candidate 0, theorem, label=integral_cos_sq_tendsto_half_measure): \begin{theorem}[integral_cos_sq_tendsto_half_measure] If $f$ is integrable on $[0, 2\pi]$,
                                                                                    then $\int_0^{2\pi} f(x) e^{-inx} dx \to 0$ as $|n| \to \infty$. Show as a consequence that
                                                                                    if $E$ is a measurable subset of $[0, 2\pi]$, then \[ \int_E \cos^2(nx + u_n) dx \to
                                                                                    \frac{m(E)}{2}, \quad \text{as } n \to \infty \] for any sequence $\{u_n\}$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
