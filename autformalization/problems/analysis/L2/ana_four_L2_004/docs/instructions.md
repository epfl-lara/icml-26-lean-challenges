# ShadowBench Instructions: `analysis/L2/ana_four_L2_004`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
```

## Expected Declaration Names

- `MeasureTheory.Integrable.fourierInv_fourier_eq`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
