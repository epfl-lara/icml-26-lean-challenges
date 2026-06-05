# Formalization Blueprint: `analysis/L2/ana_four_L2_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Inventory

### line-17

- Source inventory entry: line-17
- Source inventory entry: `line-17`
- Kind: theorem
- Source locator: `line-17`
- Source file/range: `docs/source.tex` lines 17--19
- Required named theorem: `MeasureTheory.Integrable.fourierInv_fourier_eq`
- Planned Lean declaration: `ShadowBench.Source.line17_fourierInv_fourier_eq`

## Generated File Layout

- `ShadowBench/Source/Main.lean`: imports the Mathlib module containing the required named theorem and declares the local proof-queue wrapper `ShadowBench.Source.line17_fourierInv_fourier_eq` with a `by sorry` proof placeholder.
- `ShadowBench/Source.lean`: generated submodule aggregator importing `ShadowBench.Source.Main`.
- `ShadowBench.lean`: root project module importing `ShadowBench.Source`, so project-level builds cover the generated target module.

## Import Plan

```lean
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
```

## Suggested Search Modules

- `Mathlib.Analysis.Fourier.Inversion`: source of `MeasureTheory.Integrable.fourierInv_fourier_eq` and related Fourier inversion lemmas.
- `Mathlib.Analysis.Fourier.Notation`: notation and Fourier transform/inverse transform classes.
- `Mathlib.MeasureTheory.Function.L1Space.Integrable`: definition and API for `MeasureTheory.Integrable`.

## Required Names

- `MeasureTheory.Integrable.fourierInv_fourier_eq` (imported from Mathlib; not redeclared locally to avoid a name clash)
- `ShadowBench.Source.line17_fourierInv_fourier_eq` (local source-wrapper declaration for the prover queue)

## Local and Mathlib Search Summary

- `lean_search` for `MeasureTheory.Integrable.fourierInv_fourier_eq` found the required name in the local skeletons.
- Semantic `lean_search` for the Fourier inversion statement found the Mathlib declaration `MeasureTheory.Integrable.fourierInv_fourier_eq` in `Mathlib.Analysis.Fourier.Inversion`, with related aliases and continuous/global variants.
- Direct Mathlib source inspection confirms the declaration at `Mathlib/Analysis/Fourier/Inversion.lean` lines 162--169.

## Candidate Skeletons

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose a real-valued statement using `FourierTransform f` and contain an invalid placeholder hypothesis name `***`; they were not adopted.
- `docs/skeletons/Skeleton4.lean` proposes the closest candidate shape: a complex-valued pointwise Fourier inversion theorem on a finite-dimensional real inner product space with integrability of `f` and `𝓕 f` and continuity at `v`.
- The final statement uses the existing Mathlib theorem and a local wrapper instead of copying a skeleton verbatim, because Mathlib already provides the required declaration name and a slightly more general codomain.

## Source Statement Inventory

### line-17

- Planned Lean declarations: `line17_fourierInv_fourier_eq`
- Source inventory entry: `line-17`
- Source inventory label: `line-17`
- Source label: `line-17`
- Label: `line-17`
- Source locator: `docs/source.tex:line-17` (lines 17--19)
- Source file/range: `docs/source.tex` lines 17--19.
- Source statement: Let `f` be an integrable function on a finite-dimensional real inner product space. If its Fourier transform `𝓕 f` is also integrable, then at every point where `f` is continuous, the inverse Fourier transform of `𝓕 f` equals `f` itself: `𝓕⁻ (𝓕 f) v = f v` for all continuity points `v` of `f`.
- Required named theorem: imported declaration `MeasureTheory.Integrable.fourierInv_fourier_eq` from `Mathlib.Analysis.Fourier.Inversion`. No local theorem with the same fully-qualified name is redeclared, because that would clash with the imported Mathlib declaration required by the source and instructions.
- Lean statement used for coverage:

```lean
theorem ShadowBench.Source.line17_fourierInv_fourier_eq
    {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : V → E} (hf : Integrable f) (hFf : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) :
    𝓕⁻ (𝓕 f) v = f v
```

- Dependencies: `MeasureTheory.Integrable`, Fourier transform notation `𝓕`, inverse Fourier transform notation `𝓕⁻`, finite-dimensional real inner product space structure on `V`, Borel/measurable structure on `V`, complete complex normed codomain `E`, `ContinuousAt` at the evaluation point, and the imported theorem `MeasureTheory.Integrable.fourierInv_fourier_eq` for the future proof.
- Skeleton candidate used: `Skeleton4.lean` as a statement-shape hint only; the actual declaration follows the existing Mathlib theorem.
- Formal statement review: The Lean statement preserves the source quantifier structure by taking an arbitrary finite-dimensional real inner product domain `V`, an arbitrary function `f`, hypotheses `Integrable f` and `Integrable (𝓕 f)`, an arbitrary point `v`, and the pointwise continuity hypothesis `ContinuousAt f v`, then concluding `𝓕⁻ (𝓕 f) v = f v`.
- Source qualifiers:
  - Mathematical object class: function on a finite-dimensional real inner product space.
  - Quantifier order: function and hypotheses first, then an arbitrary continuity point `v`.
  - Parameter domain: finite-dimensional real inner product space, with Lean's Borel/measurable typeclass infrastructure made explicit.
  - Output codomain: source does not explicitly specify; Lean uses a complete complex normed codomain `E`, covering the usual complex-valued case and more general vector-valued versions.
  - Equality condition: pointwise equality of inverse Fourier transform after Fourier transform with the original function at `v`.
  - Side conditions: `Integrable f`, `Integrable (𝓕 f)`, and `ContinuousAt f v`.
  - Follow-on claims: none in the source.
- Lean coverage: exact mathematical coverage of the named Fourier inversion statement, with Lean explicitness for measure/topological typeclasses and a general complete complex normed codomain. The required theorem name is supplied by Mathlib, and the local wrapper in `Main.lean` mirrors the same statement for source-map and proof-queue purposes.
- Scope changes: no weakening. The only changes are explicit Lean infrastructure assumptions and a codomain generalization because the source leaves the codomain implicit; no richer source representation or parameter-domain bridge is stated in the source.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: the source document gives no proof after the theorem statement.
- Source proof / prover notes: Mathlib proves the imported theorem by comparing two limits built from Gaussian approximate identities. The proof shows a Gaussian-smoothed integral tends both to `𝓕⁻ (𝓕 f) v` using integrability of `𝓕 f` and to `f v` using continuity at `v`, then uses uniqueness of limits. A future prover can close the local wrapper with `hf.fourierInv_fourier_eq hFf hv`.

## Handoff Notes

- Local proof obligation currently drafted for later proof workflow: `ShadowBench.Source.line17_fourierInv_fourier_eq`.
- Independent statement/source review should confirm that the imported required theorem plus local wrapper is acceptable coverage for `line-17` before proof handoff.
- Suggested proof command after review: `/prove ShadowBench/Source/Main.lean`.
