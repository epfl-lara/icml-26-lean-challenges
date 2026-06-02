# ShadowBench Instructions: `analysis/L2/ana_comp_L2_001`

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
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
```

## Expected Declaration Names

- `integral_boundary_rect_of_hasFDerivAt_real_off_countable`

## Formalization Rules

```text
open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology

/-
Formalize in Lean the Theorem (integral_boundary_rect_of_hasFDerivAt_real_off_countable) from Text.

The theorem must be named `integral_boundary_rect_of_hasFDerivAt_real_off_countable`.
   Matched text (candidate 0, theorem, label=integral_boundary_rect_of_hasFDerivAt_real_off_countable): \begin{theorem}[integral_boundary_rect_of_hasFDerivAt_real_off_countable] Let $f :
                                                                                                        \mathbb{C} \to E$ be a function with values in a real normed vector space $E$. Let
                                                                                                        $z^{\ast}, w^{\ast} \in \mathbb{C}$. Assume the following: \begin{enumerate} \item The
                                                                                                        function $f$ is continuous on the closed rectangle \[ R := [\Re(z^{\ast}),\, \Re(w^{\ast})]
                                                                                                        \times [\Im(z^{\ast}),\, \Im(w^{\ast})] \subset \mathbb{C}. \] \item There…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
