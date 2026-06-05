# Formalization Blueprint: `analysis/L2/ana_four_L2_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Import Plan

Direct imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
```

## Suggested Search Modules

Non-gating search hints for later proof work:

- `Mathlib.Analysis.Fourier.FourierTransform`: search found `Real.instFourierTransform`, `Real.instFourierTransformInv`, `Real.fourier_eq`, and `Real.fourierIntegralInv_eq'`.
- Dominated-convergence lemmas in `MeasureTheory` for Bochner integrals, especially theorem names containing `dominated_convergence` and `tendsto_integral`.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one-file source-fidelity draft containing two companion Fourier-expression definitions and the two expected source-backed lemma declarations.
- `ShadowBench/Source.lean`: root project module; currently imports `ShadowBench.Source.Main`, so project-level builds cover the generated target module.

No additional Lean file split is planned before statement/source review; the source has only two named items.

## Candidate Skeletons Reviewed

- `docs/skeletons/Skeleton1.lean`: gave useful companion definitions and the real-exponential convergence shape, but did not include the required `ABM_analysis_L2_ana_four_L2_002_item_1` declaration.
- `docs/skeletons/Skeleton2.lean` and `docs/skeletons/Skeleton3.lean`: added the expected `ABM_analysis_L2_ana_four_L2_002_item_1` name only as `True`; that weakens the source and was not adopted.
- `docs/skeletons/Skeleton4.lean`: closest to the final source statements. The final draft adopts its real-exponential convergence shape and expected names, but uses explicit companion definitions for the Fourier/inverse-Fourier display in line-17 rather than the skeleton's integrability-only statement.

## Declarations and Definitions

- `sourceFourierTransform`: implemented companion definition for the displayed Fourier-transform integral in `line-17`, parameterized by the source measure `μ`.
- `sourceInverseFourierTransform`: implemented companion definition for the displayed inverse-Fourier-transform integral in `line-17`, parameterized by the source measure `μ`.
- `ABM_analysis_L2_ana_four_L2_002_item_1`: source-backed lemma recording that the two companion definitions unfold to the displayed formulas.
- `tendsto_integral_cexp_sq_smul`: source-backed lemma stating the dominated-convergence limit of Gaussian cutoffs.

## Source Statement Inventory

### line-17

- Kind: lemma environment in `docs/source.tex`, lines 17--28.
- Source locator: `line-17` (`docs/source.tex`, lines 17--28).
- Source statement:

```text
Let V be a finite-dimensional real inner product space, equipped with its Borel sigma-algebra and a measure dv.
Let E be a complex normed vector space (assumed complete when needed), and let f : V -> E.
We write the Fourier transform and inverse Fourier transform as follows:
  (F f)(w) = ∫_V e^{-2π i <w,x>} f(x) dx,
  (F^- g)(v) = ∫_V e^{2π i <w,v>} g(w) dw.
```

- Planned Lean declarations: `ABM_analysis_L2_ana_four_L2_002_item_1`.
- Companion declarations used: `sourceFourierTransform`, `sourceInverseFourierTransform`.
- Skeleton candidate used: influenced by Skeleton1/Skeleton4 definitions, but not copied; Skeleton2/Skeleton3 `True` stubs were rejected as non-fidelitous.
- Dependencies: `MeasureTheory.Measure`, Bochner integral notation, `Complex.exp`, real inner product notation `⟪_, _⟫_ℝ`, finite-dimensional real inner-product typeclasses, complex normed-space typeclasses.
- Lean statement:

```lean
lemma ABM_analysis_L2_ana_four_L2_002_item_1
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure V) (f g : V → E) :
    (∀ w : V, sourceFourierTransform μ f w =
      ∫ x : V, Complex.exp ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((inner ℝ w x) : ℂ)) • f x ∂μ) ∧
    (∀ v : V, sourceInverseFourierTransform μ g v =
      ∫ w : V,
        Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((inner ℝ w v) : ℂ)) • g w ∂μ)
```

- Formal statement review: the source item is definitional notation rather than a mathematical proposition. The Lean draft implements the two displayed integrals as companion definitions and gives the required named lemma as the definitional bridge to those formulas.
- Source qualifiers:
  - Object class: finite-dimensional real inner product space `V` with Borel measurable structure and measure `dv`.
  - Quantifier order and domains: choose the ambient `V`, the source measure, the complex target `E`, then functions `f : V → E` and the implicitly used inverse-transform input `g : V → E`; point variables `w v : V` and integration variables `x w : V` range over the same source space.
  - Output codomain: both transform values and Bochner integrals are `E`-valued.
  - Side conditions: `E` is a complex normed vector space and is complete when the displayed Bochner integrals require completeness.
  - Equality/image condition: Fourier and inverse-Fourier expressions equal the displayed integrals with phases `-2π i ⟪w,x⟫` and `+2π i ⟪w,v⟫`.
  - Follow-on claims: none beyond introducing this notation/formula bridge.
- Lean coverage:
  - Typeclasses and `μ : Measure V` cover the source object class and measure.
  - `sourceFourierTransform μ f w` covers `(𝓕 f)(w)` for the measure-parameterized source notation.
  - `sourceInverseFourierTransform μ g v` covers `(𝓕⁻ g)(v)`.
  - The named lemma exposes both displayed formulas as equalities.
- Scope changes:
  - The source text does not explicitly quantify `g` before writing `(𝓕⁻ g)(v)`; Lean adds `g : V → E` explicitly.
  - Mathlib's global Fourier-transform notation is not used in the statement because the source explicitly carries a measure `dv`; companion definitions record the representation bridge instead of silently switching to Mathlib's volume-based transform.
  - `CompleteSpace E` is included, matching the source parenthetical “assumed complete when needed” for Bochner integrals.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no source proof is provided because the item defines notation. The eventual proof should unfold `sourceFourierTransform` and `sourceInverseFourierTransform`; both goals should be definitional equalities.

### line-31

- Kind: lemma environment in `docs/source.tex`, lines 31--37; proof lines 37--82.
- Source locator: `line-31` (`docs/source.tex`, lines 31--37; proof lines 37--82).
- Source statement:

```text
If f is integrable, then as c tends to infinity,
  ∫_V e^{-c^{-1} ||v||^2} f(v) dv  -->  ∫_V f(v) dv.
```

- Planned Lean declarations: `tendsto_integral_cexp_sq_smul`.
- Skeleton candidate used: Skeleton4's statement shape was closest and shaped the final declaration; the final draft keeps the source's finite-dimensional real inner-product setting, arbitrary measure `μ`, complex complete codomain, and real exponential scalar.
- Dependencies: source assumptions from line-17, `Integrable f μ`, Bochner integral notation, `Filter.Tendsto`, `Filter.atTop`, `nhds`, `Real.exp`.
- Lean statement:

```lean
lemma tendsto_integral_cexp_sq_smul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure V) (f : V → E) (hf : Integrable f μ) :
    Tendsto (fun c : ℝ => ∫ v : V, Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v ∂μ)
      atTop (𝓝 (∫ v : V, f v ∂μ))
```

- Formal statement review: Lean encodes “as `c` tends to infinity” as `Tendsto ... atTop`. The integrand uses the real scalar `Real.exp (-c⁻¹ * ‖v‖ ^ 2)` acting on the complex normed vector value `f v`, matching the source's real Gaussian factor.
- Source qualifiers:
  - Same source object class as line-17: finite-dimensional real inner product `V`, Borel measurable structure, measure `dv`; complex normed/complete `E`.
  - Assumption: `f` is integrable with respect to the source measure.
  - Parameter domain: `c : ℝ` tends to `+∞`.
  - Output codomain: each Bochner integral is `E`-valued.
  - Equality/limit condition: integrals of Gaussian-cutoff scalar multiples converge to the integral of `f`.
  - Side conditions and follow-on claims: no additional source side condition beyond integrability and the ambient completeness needed for Bochner integration; the proof's eventual restriction to `c ≥ 0` is a dominated-convergence proof step encoded by convergence along `atTop`, not an extra statement hypothesis.
- Lean coverage:
  - Typeclasses and `μ : Measure V` cover the source ambient space and measure.
  - `hf : Integrable f μ` covers “If `f` is integrable”.
  - `Tendsto ... atTop (𝓝 ...)` covers convergence as `c → +∞`.
  - The Bochner integral expression exactly carries `Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v` and target integral `∫ v, f v ∂μ`.
- Scope changes:
  - The source leaves the measure notation implicit between `dv` and `dμ`; Lean names the measure `μ` consistently.
  - No mathematical weakening or strengthening is intended.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
We shall apply the dominated convergence theorem.

(i) For each fixed v ∈ V, we have
  e^{-c^{-1}||v||^2} f(v) → f(v)
as c → +∞. Moreover, for all sufficiently large c,
  ||e^{-c^{-1}||v||^2} f(v)|| ≤ ||f(v)||.

(ii) For each c ∈ ℝ, the function
  v ↦ e^{-(1/c)||v||^2}
is continuous, hence measurable. Since f is integrable, it is almost everywhere strongly measurable. Therefore the product
  v ↦ e^{-(1/c)||v||^2} f(v)
is almost everywhere strongly measurable for each c.

(iii) Restrict to c ≥ 0. Then for all v ∈ V,
  ||e^{-(1/c)||v||^2} f(v)||
  = |e^{-(1/c)||v||^2}| ||f(v)||
  = e^{-(1/c)||v||^2} ||f(v)||
  ≤ ||f(v)||.
The function v ↦ ||f(v)|| is integrable by assumption, so it dominates the integrand for all sufficiently large c.

Now, we may apply the dominated convergence theorem and conclude that
  lim_{c → +∞} ∫_V e^{-(1/c)||v||^2} f(v) dμ(v) = ∫_V f(v) dμ(v),
as claimed.
```

- Prover notes: prove pointwise convergence of the scalar factor to `1` along `atTop`, then use dominated convergence for Bochner integrals. The domination is `‖Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v‖ ≤ ‖f v‖` eventually because `0 ≤ Real.exp _` and for eventually positive `c`, `Real.exp (-c⁻¹ * ‖v‖ ^ 2) ≤ 1`. Measurability follows from continuity of the scalar factor and a.e. strong measurability from `hf`.
