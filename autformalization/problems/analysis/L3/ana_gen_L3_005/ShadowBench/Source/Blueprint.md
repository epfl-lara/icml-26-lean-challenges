# Formalization Blueprint: `analysis/L3/ana_gen_L3_005`

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
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
```

## Required Names

- `integral_cos_sq_tendsto_half_measure`

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
