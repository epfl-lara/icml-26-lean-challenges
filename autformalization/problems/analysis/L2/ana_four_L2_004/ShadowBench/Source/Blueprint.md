# Formalization Blueprint: `analysis/L2/ana_four_L2_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
```

## Required Names

- `MeasureTheory.Integrable.fourierInv_fourier_eq`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
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
Formalize in Lean the Theorem (MeasureTheory.Integrable.fourierInv_fourier_eq) from Text.

The theorem must be named `MeasureTheory.Integrable.fourierInv_fourier_eq`.
   Matched text (candidate 0, theorem, label=MeasureTheory.Integrable.fourierInv_fourier_eq): \begin{theorem}[MeasureTheory.Integrable.fourierInv_fourier_eq] Let $f$ be an integrable
                                                                                              function on a finite-dimensional real inner product space. If its Fourier transform
                                                                                              $\mathcal{F} f$ is also integrable, then at every point where $f$ is continuous, the inverse
                                                                                              Fourier transform of $\mathcal{F} f$ equals $f$ itself; that is,
                                                                                              $\mathcal{F}^{-1}(\mathcal{F} f)(v) = f(v)$ for all continuity points $v$ of $f$. \end{t…
-/
```
