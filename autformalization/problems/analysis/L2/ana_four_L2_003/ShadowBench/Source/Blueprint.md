# Formalization Blueprint: `analysis/L2/ana_four_L2_003`

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

- `tendsto_integral_gaussian_smul`

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
Formalize in Lean the Lemma (tendsto_integral_gaussian_smul) from Text.

The lemma must be named `tendsto_integral_gaussian_smul`.
   Matched text (candidate 0, theorem, label=tendsto_integral_gaussian_smul): \begin{theorem}[tendsto_integral_gaussian_smul] Suppose that $f\in L^{1}(V;E)$ and $f$ is
                                                                              continuous at $v\in V$. Then we have: \[ \lim_{c\to\infty} \int_{w\in V} \Bigl((\pi
                                                                              c)^{\frac{\dim_{\mathbb R}V}{2}}\; e^{-\pi^{2}c\,\|v-w\|^{2}}\Bigr)\, f(w)\,d\mu(w) = f(v),
                                                                              \] under the hypotheses that $f$ is integrable and continuous at $v$. \end{theorem}
-/
```
