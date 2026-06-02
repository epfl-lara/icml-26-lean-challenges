# Formalization Blueprint: `analysis/L2/ana_comp_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

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

## Required Names

- `integral_boundary_rect_of_hasFDerivAt_real_off_countable`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

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
