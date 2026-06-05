# Formalization Blueprint: `probability/L3/prob_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`
  - Direct imports: `Mathlib`
  - Defines `BuffonNeedleExperiment` as the coordinate model for a needle of length `ℓ` and ruled-line spacing `d` with `0 < ℓ` and `ℓ ≤ d`.
  - Defines `buffonNeedleExperiment` for building that model from the theorem parameters.
  - Defines `BuffonNeedleExperiment.sampleSpace`, `BuffonNeedleExperiment.crossingEvent`, and `BuffonNeedleExperiment.crossingProbability`.
  - States the source theorem as `BuffonNeedle` with a `by sorry` proof skeleton.

The root module already imports the generated target through `ShadowBench.lean -> ShadowBench/Source.lean -> ShadowBench/Source/Main.lean`, so the default `ShadowBench` build target covers this file.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

These are search/proof hints only, not required direct imports in the draft because `Mathlib` is the allowed starting import.

- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` for Lebesgue volume and interval-volume facts such as `MeasureTheory.Measure.real` and `Real.volume_pi_Ioc_toReal`.
- `Mathlib.MeasureTheory.Constructions.Pi` and product-measure facts such as `MeasureTheory.volume_pi_pi`.
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` for `Real.sin_nonneg_of_nonneg_of_le_pi` and sine endpoint facts.
- Interval-integral facts for computing `∫ θ in 0..Real.pi, Real.sin θ` during the prover phase.

## Required Names

- `BuffonNeedle`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` all suggest the parameter order `(ℓ d : ℝ) (h_pos : 0 < ℓ) (h_ge : ℓ ≤ d)` and theorem name `BuffonNeedle`.
- `Skeleton4.lean` has the same intended theorem shape but contains malformed trailing syntax.
- The skeletons introduce an abstract `buffon_probability` with a `sorry` definition. That construction was not adopted because definition/structure construction gaps block proof handoff. The final draft instead implements explicit coordinate-space definitions for the sample space, crossing event, and probability ratio, while preserving the source theorem name and parameter order.

## Statement Inventory

### Source theorem: `BuffonNeedle`

- Planned Lean declaration: `BuffonNeedle`
- Source locator: `docs/source.tex`, theorem text headed `Theorem(`BuffonNeedle`)` after `\maketitle`.
- Skeleton candidate used: parameter order and side conditions shaped by `Skeleton1.lean`/`Skeleton2.lean`/`Skeleton3.lean`; abstract probability definition rejected and replaced by concrete measure-theoretic definitions.
- Dependencies / companion declarations:
  - `BuffonNeedleExperiment`: structure representing the source coordinate model with fields `needleLength`, `lineSpacing`, `needleLength_pos`, and `needleLength_le_lineSpacing`.
  - `buffonNeedleExperiment`: constructor from source parameters `(ℓ d : ℝ) (0 < ℓ) (ℓ ≤ d)`.
  - `BuffonNeedleExperiment.sampleSpace`: the rectangle `[0,d] × [0,π]` for midpoint height and angle.
  - `BuffonNeedleExperiment.crossingEvent`: points `(y, θ)` satisfying `y ≤ ℓ sin θ / 2` or `d - ℓ sin θ / 2 ≤ y`.
  - `BuffonNeedleExperiment.crossingProbability`: Lebesgue-area ratio `volume(sampleSpace ∩ crossingEvent) / volume(sampleSpace)` converted to `ℝ`.
- Lean statement:
  ```lean
  theorem BuffonNeedle (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
      BuffonNeedleExperiment.crossingProbability (buffonNeedleExperiment ℓ d hℓ hℓd) =
        2 * ℓ / (Real.pi * d) := by
    sorry
  ```
- Formal statement review:
  - The source theorem states the probability that a short needle of length `ℓ` crosses equally spaced parallel lines of spacing `d ≥ ℓ` is `2ℓ/(π d)`.
  - The Lean theorem quantifies over real parameters `ℓ` and `d`, assumes `0 < ℓ` to formalize the source phrase “length”/“short needle”, and assumes `ℓ ≤ d` to match `d ≥ ℓ`. Positivity of `d` follows from these assumptions.
  - The probability is not an uninterpreted symbol: it is defined as the normalized Lebesgue measure of the crossing event in the coordinate model used by the source proof.
- Source qualifiers:
  - Mathematical object class: a short needle and an equally spaced ruled paper, modeled by `BuffonNeedleExperiment`.
  - Quantifier order: choose needle length `ℓ`, line spacing `d`, then assumptions `0 < ℓ` and `ℓ ≤ d`.
  - Parameter domain: real-valued lengths/spacings with positive needle length and spacing at least needle length.
  - Probability model: uniform distribution over `[0,d] × [0,π]` where first coordinate is midpoint height above the lower ruled line and second coordinate is the needle angle.
  - Event condition: crossing occurs when `y ≤ ℓ sin θ / 2` or `d - ℓ sin θ / 2 ≤ y`.
  - Output codomain: real probability value.
  - Equality/image condition: this probability equals `2 * ℓ / (Real.pi * d)`.
  - Follow-on claims: no additional corollaries or named consequences are present in the source.
- Lean coverage:
  - Object class and parameter side conditions are covered by `BuffonNeedleExperiment` and `buffonNeedleExperiment`.
  - Uniform coordinate rectangle is covered by `BuffonNeedleExperiment.sampleSpace`.
  - Crossing condition is covered by `BuffonNeedleExperiment.crossingEvent`.
  - Probability value is covered by `BuffonNeedleExperiment.crossingProbability` as a normalized Lebesgue-volume ratio.
  - Formula equality is covered by theorem `BuffonNeedle`.
- Scope changes:
  - The physical experiment is formalized through the coordinate-space representation explicitly assumed in the source proof rather than by a separate geometric model of ruled paper in the plane. The bridge is recorded by `BuffonNeedleExperiment`, `sampleSpace`, and `crossingEvent`.
  - Boundary inequalities use `≤` instead of the source words “lower than”/“higher than”; this does not change the Lebesgue probability but is a modeling choice the prover may need to use as a measure-zero boundary simplification.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  > We can assume the uniform probability distribution over `[0, d] × [0, π]`, where each component means the midpoint position relative to the closest lower line and the angle relative to a fixed direction of the ruling respectively. Then the needle crosses a line with angle `θ` exactly when its height `y` of midpoint is lower than `ℓ sin θ / 2` or higher than `d - ℓ sin θ / 2`. Thus the marginal probability for `θ` is `ℓ sin θ / d`. Now we get the probability as the average of probability over `θ`, namely `(1 / π) ∫_0^π (ℓ sin θ / d) dθ = 2ℓ/(π d)`.
- Source proof / prover notes:
  1. Unfold `crossingProbability`, `sampleSpace`, and `crossingEvent`.
  2. Use Fubini/product-measure reasoning on `[0,d] × [0,π]`.
  3. For fixed `θ ∈ [0,π]`, use `0 ≤ sin θ` and `ℓ ≤ d` to show the crossing slice in the `y` direction has length `ℓ * sin θ`; the two boundary intervals meet only in the limiting case where the length is `d`.
  4. Divide the slice length by `d` for the conditional probability, then average over `θ ∈ [0,π]`.
  5. Compute `(1 / Real.pi) * ∫ θ in 0..Real.pi, (ℓ * Real.sin θ / d) = 2 * ℓ / (Real.pi * d)` using `∫ sin = 2`, `Real.pi_pos`, and field simplification.
