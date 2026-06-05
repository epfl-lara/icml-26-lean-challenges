# Formalization Blueprint: `analysis/L3/ana_gen_L3_008`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed definition bridge `intervalTailIntegral` and theorem skeleton `intervalIntegrable_g_and_integral_g_eq_integral`.
- `ShadowBench/Source.lean`: already imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: already imports `ShadowBench.Source`, so plain project builds cover the generated target module.

## Import Plan

```lean
import Mathlib
```

The direct Lean import block of `ShadowBench/Source/Main.lean` is exactly the import plan above.

## Suggested Search Modules

Non-gating search hints for the later prover run:

- `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` for `IntervalIntegrable`, interval-integral notation, and interval integral congruence/linearity lemmas.
- `Mathlib.MeasureTheory.Integral.Prod` and `Mathlib.MeasureTheory.Measure.Prod` for Fubini/Tonelli style exchange of integrals.
- `Mathlib.Analysis.SpecialFunctions.Integrability.Basic` for local integrability of reciprocal/power functions away from zero.

## Required Names

- `intervalIntegrable_g_and_integral_g_eq_integral`

## Source Inventory

- `line-17` (theorem, `docs/source.tex` lines 17-26; proof environment lines 28-60) maps to Lean theorem `intervalIntegrable_g_and_integral_g_eq_integral` and definition bridge `intervalTailIntegral`.

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose a zero-at-0 extension `if x = 0 then 0 else ∫ t in x..b, f t / t`. This is less faithful to the source because it assigns the integral formula to negative `x` and to `x > b`, where the source only states it for `0 < x ≤ b`.
- `docs/skeletons/Skeleton4.lean` proposes the source-domain guard `if 0 < x ∧ x ≤ b then ∫ t in x..b, f t / t else 0`. The final draft follows this candidate's domain guard but factors it into the definition bridge `intervalTailIntegral` for readability and proof reuse.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source kind: theorem
- Source title: theorem `intervalIntegrable_g_and_integral_g_eq_integral`.
- Planned Lean declaration: `intervalIntegrable_g_and_integral_g_eq_integral`
- Source label: `line-17`
- Source locator: `line-17` (`docs/source.tex`, theorem block lines 17-26; proof environment lines 28-60).
- Planned Lean declarations:
  - Definition bridge: `intervalTailIntegral`.
  - Theorem skeleton: `intervalIntegrable_g_and_integral_g_eq_integral`.
- Skeleton candidate used: shaped by `docs/skeletons/Skeleton4.lean`; see candidate review above.
- Dependencies: `IntervalIntegrable`, interval-integral notation `∫ x in a..b, ...`, Lebesgue measure `volume`, real arithmetic/order, later Tonelli/Fubini and interval-integral linearity/congruence lemmas.
- Source statement: Suppose `f` is integrable on `[0, b]`, and `g(x) = ∫_x^b f(t) / t dt` for `0 < x ≤ b`. Prove that `g` is integrable on `[0, b]` and `∫_0^b g(x) dx = ∫_0^b f(t) dt`.
- Lean statement summary: for real `b` and real-valued `f`, assuming `hb : 0 < b` and `hf : IntervalIntegrable f volume 0 b`, the zero-extension
  `intervalTailIntegral f b x = if 0 < x ∧ x ≤ b then ∫ t in x..b, f t / t else 0`
  is interval-integrable from `0` to `b`, and its interval integral over `0..b` equals the interval integral of `f` over `0..b`.
- Formal statement review: `IntervalIntegrable f volume 0 b` formalizes Lebesgue integrability on the interval `[0,b]` using Mathlib's interval-integral API. The theorem conclusion contains both requested claims: interval integrability of the formalized `g` and equality of interval integrals.
- Source qualifiers:
  - Mathematical object class: real-valued functions `f, g : ℝ → ℝ` with Lebesgue interval integration on a real interval.
  - Quantifier order: for real `b` and real-valued `f`, assume the interval is positive and `f` is integrable on `[0,b]`; define/choose `g` by the displayed tail-integral formula on `0 < x ≤ b`; then assert the two output claims.
  - Parameter domain: interval endpoints are `0` and `b` with the source's positive-interval convention `0 < b`; the displayed formula for `g` is only required on `0 < x ≤ b`.
  - Output codomain: `f`, the chosen total representative of `g`, and all interval integrals are real-valued.
  - Definition/equality condition: on every `x` with `0 < x ∧ x ≤ b`, `g x = ∫ t in x..b, f t / t`; the source does not specify values of `g` at `x = 0` or outside this domain.
  - Side conditions: `f` is integrable on `[0,b]`; for each source-domain tail integral, the denominator variable is away from `0` because the lower limit satisfies `x > 0`.
  - Follow-on claims: `g` is integrable on `[0,b]`, and `∫_0^b g(x) dx = ∫_0^b f(t) dt`.
- Lean coverage:
  - `intervalTailIntegral` is the companion total-function bridge for the source-defined `g`; unfolding the definition under `0 < x ∧ x ≤ b` gives exactly `∫ t in x..b, f t / t`, and outside that source domain it uses `0`.
  - The theorem quantifies `b : ℝ` and `f : ℝ → ℝ`, assumes `hb : 0 < b` and `hf : IntervalIntegrable f volume 0 b`, and concludes both `IntervalIntegrable (intervalTailIntegral f b) volume 0 b` and `∫ x in 0..b, intervalTailIntegral f b x = ∫ t in 0..b, f t`.
  - `volume`, `IntervalIntegrable`, and `∫ x in 0..b` formalize the source's real Lebesgue interval integrability and interval integrals on `[0,b]`.
- Scope changes: explicit assumption `hb : 0 < b` records the source's implicit positive-interval convention; the partially specified source function `g` is represented by the zero-extension `intervalTailIntegral`, whose values outside `0 < x ≤ b`, including the endpoint `x = 0`, are a representation bridge and do not change Lebesgue interval integrability or the interval integral over `[0,b]` except on a null endpoint; no other weakening, strengthening, or scope alteration.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: We first assume that `f(x) ≥ 0`. Then `g(x) ≥ 0` as well. This is enough, since in general we can write `f = f⁺ - f⁻`, and use the linearity of the Lebesgue integral. For `f ≥ 0`, Tonelli's theorem allows us to interchange the order of integration. Thus
  `∫_0^b g(x) dx = ∫_0^b ∫_x^b f(t)/t dt dx = ∫_0^b ∫_0^b (f(t)/t) χ_{t≥x} dx dt = ∫_0^b (f(t)/t) ∫_0^b χ_{x≤t} dx dt = ∫_0^b (f(t)/t) ∫_0^t dx dt = ∫_0^b (f(t)/t) t dt = ∫_0^b f(t) dt`. Since `f` is integrable on `[0,b]`, the last integral is finite, hence `g` is integrable on `[0,b]`. Finally apply the same argument to `f⁺` and `f⁻`, and use linearity to obtain the signed-function result.
- Prover notes: A later proof should probably first prove the nonnegative version using Tonelli over the region `{(x,t) | 0 < x ∧ x ≤ t ∧ t ≤ b}` or an indicator over `[0,b] × [0,b]`. The inner `x`-integral of the indicator `{x | x ≤ t}` over `[0,b]` is `t` for `0 ≤ t ≤ b`. Extend to signed real-valued `f` by positive/negative parts or by integrability/Bochner Fubini with an integrable majorant. Use interval-integral congruence to ignore the zero-extension outside `(0,b]` and endpoint `0`.

## Handoff Checklist

- [x] Source document inspected with `formalization_document_inspect`.
- [x] Companion instructions and candidate skeletons reviewed.
- [x] Blueprint source inventory includes `line-17`, source qualifiers, Lean coverage, scope changes, complete source proof text, and prover notes.
- [x] Target Lean file begins with imports before comments/declarations.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Proof phase has removed theorem `sorry` placeholders.
