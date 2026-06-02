# Formalization Blueprint: `analysis/L2/ana_four_L2_002`

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
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
```

## Required Names

- `ABM_analysis_L2_ana_four_L2_002_item_1`
- `tendsto_integral_cexp_sq_smul`

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
open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

/-
Formalize in Lean the following named items from Text.

1. Lemma (ABM_analysis_L2_ana_four_L2_002_item_1)
   The lemma must be named `ABM_analysis_L2_ana_four_L2_002_item_1`.
   Matched text (candidate 0, lemma): \begin{lemma} Let $V$ be a finite-dimensional real inner product space, equipped with its
                                      Borel $\sigma$-algebra and a measure $dv$. Let $E$ be a complex normed vector space (assumed
                                      complete when needed), and let $f : V \to E$. We write the Fourier transform and inverse
                                      Fourier transform as follows: \[ (\mathcal{F}f)(w) \;=\; \int_V e^{-2\pi i \langle
                                      w,x\rangle}\, f(x)\,dx, \qquad (\mathcal{F}^{-}g)(v) \;=\; \int_…
2. Lemma (tendsto_integral_cexp_sq_smul)
   The lemma must be named `tendsto_integral_cexp_sq_smul`.
   Matched text (candidate 1, theorem, label=tendsto_integral_cexp_sq_smul): \begin{theorem}[tendsto_integral_cexp_sq_smul] If $f$ is integrable, then as $c$ tends to
                                                                             infinity, \[ \int_V e^{-c^{-1}\|v\|^2}\, f(v)\,dv \;\xrightarrow{}\; \int_V f(v)\,dv . \]
                                                                             \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
