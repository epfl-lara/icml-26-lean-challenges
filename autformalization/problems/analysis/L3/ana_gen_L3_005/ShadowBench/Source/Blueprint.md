# Formalization Blueprint: `analysis/L3/ana_gen_L3_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one-file formalization of source theorem block `line-17`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

No split into additional generated files is useful for this one-theorem source document.

## Import Plan

```lean
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
```

The import plan lists exactly the direct imports used by `ShadowBench/Source/Main.lean`.

## Suggested Search Modules

These are prover search hints, not direct-import requirements.

- `Mathlib.Analysis.Fourier.RiemannLebesgueLemma`, especially `Real.tendsto_integral_exp_smul_cocompact`.
- Interval integral facts around `IntervalIntegrable` and `∫ x in a..b, _`.
- Set integral and measure facts around `∫ x in E, _`, `MeasurableSet`, and `(volume E).toReal`.
- Trigonometric identities for `cos_sq`, `cos_add`, and double-angle formulas.

## Required Names

- `integral_cos_sq_tendsto_half_measure`

## Candidate Skeletons

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose a conjunction of the preliminary Riemann-Lebesgue assertion with the measurable-set cosine-square consequence. This matches the two-part source theorem block.
- `docs/skeletons/Skeleton4.lean` proposes only the consequence, but its target `(volume E).toReal / 2` is the correct real-valued Lean representation of `m(E) / 2` for a real set integral.
- Adopted skeleton influence: conjunction shape from Skeleton1-3; real measure target from Skeleton4; explicit complex coercions and norm notation adjusted for Lean elaboration.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem block `line-17`, statement lines 17-21; proof environment lines 23-37.
- Planned Lean declarations: `integral_cos_sq_tendsto_half_measure`.
- Skeleton candidate used: conjunction shape from `Skeleton1.lean`/`Skeleton2.lean`/`Skeleton3.lean`, with the `(volume E).toReal / 2` target style from `Skeleton4.lean`.
- Dependencies: `IntervalIntegrable`, interval integral notation, complex exponential `Complex.exp`, complex norm `‖_‖`, `MeasurableSet`, `Set.Icc`, set integral notation, Lebesgue measure `volume`, `Filter.Tendsto`, `Filter.atTop`, and `𝓝`.
- Formal statement review:
  - The Lean theorem packages the two source sentences as a conjunction: the preliminary Riemann-Lebesgue limit and the requested measurable-set consequence.
  - The source limit “as `|n| → ∞`” is represented by an ε-N formulation over `n : ℤ` with `(N : ℤ) ≤ |n|`; this is equivalent to the source's “provided `|n| > N`” after changing the witness bound.
  - The source integral `∫_0^{2π}` is represented by Lean interval integral notation `∫ x in (0)..(2 * Real.pi), _`.
  - The source complex exponential `e^{-inx}` is represented by `Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))`.
  - The source complex absolute value is represented by the norm `‖_‖` on `ℂ`.
  - The source measure `m(E)` is represented by `(volume E).toReal`, matching the real codomain of the set integral. The assumption `E ⊆ Set.Icc 0 (2 * Real.pi)` records membership in the bounded interval.
  - The consequence limit “as `n → ∞`” is represented by `Filter.Tendsto ... Filter.atTop` over `n : ℕ`.
- Source qualifiers:
  - Mathematical object class: an integrable function on `[0, 2π]` used in a complex Fourier integral; a measurable subset `E` of `[0, 2π]`; an arbitrary real phase sequence `{u_n}`.
  - Quantifier order: first, for every integrable `f`, the Fourier coefficient limit holds; then, as a consequence, for every measurable `E ⊆ [0, 2π]` and every sequence `u`, the cosine-square limit holds.
  - Parameter domains: Lean fixes the implicit Fourier-integrand codomain as `f : ℝ → ℂ`; `E : Set ℝ`; `u : ℕ → ℝ`; oscillation index `n : ℤ` for the `|n| → ∞` part and `n : ℕ` for the consequence.
  - Output codomain: complex-valued interval integral tending to `0` in the first clause; real-valued set integral tending to `(volume E).toReal / 2` in the consequence.
  - Equality/image condition: convergence of the Fourier integral to `0`, and convergence of the cosine-square integral over `E` to one half of the Lebesgue measure of `E`.
  - Side conditions: `IntervalIntegrable f volume 0 (2 * Real.pi)`, `MeasurableSet E`, and `E ⊆ Set.Icc 0 (2 * Real.pi)`.
  - Follow-on claims: the statement-level follow-on is exactly the measurable-set consequence. The displayed oscillatory integral estimate in the source proof is a proof intermediate, not a separate source theorem; it is preserved in the proof/prover notes rather than as a separate Lean declaration.
- Lean coverage:
  - The first conjunct covers the source Riemann-Lebesgue assertion for complex-valued interval-integrable functions on `[0, 2π]`, with the `|n| → ∞` limit expressed by the reviewed ε-N formulation over `ℤ`.
  - The second conjunct covers the measurable-set consequence for all `E : Set ℝ` satisfying `MeasurableSet E` and `E ⊆ Set.Icc 0 (2 * Real.pi)`, and for all real sequences `u : ℕ → ℝ`.
  - The target `(volume E).toReal / 2` covers the source `m(E) / 2` in the real codomain of the set integral; finiteness is represented by the bounded-subset hypothesis.
  - The nearby Lean doc comment gives the prover the source proof route: real/imaginary Riemann-Lebesgue decay, indicator specialization, the shifted oscillatory integral bound, the `cos^2` double-angle rewrite, and Tendsto arithmetic.
  - The theorem name is exactly the required source name `integral_cos_sq_tendsto_half_measure`.
- Scope changes: representation changes only; all source statement content is retained.
  - Explicit representation changes:
  - The source leaves the scalar codomain of `f` implicit; Lean uses complex-valued `f : ℝ → ℂ`, the direct codomain for multiplication by `e^{-i n x}`.
  - The source phrase “measurable subset of `[0, 2π]`” is represented by `MeasurableSet E` together with `E ⊆ Set.Icc 0 (2 * Real.pi)`.
  - The source measure notation `m(E)` is represented by `(volume E).toReal` in the real limit target.
  - The preliminary limit is expressed as an ε-N statement rather than a `Tendsto` statement over a cocompact filter on `ℤ`, matching the explicit “`|n|` large” wording and preserving the limit content.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: The source proof takes real and imaginary parts of the Riemann-Lebesgue integral to obtain decay of sine and cosine integrals, applies this to the indicator of `E`, bounds the shifted integral of `cos (2 n x + 2 u_n)` using `|cos| ≤ 1` and `|sin| ≤ 1`, rewrites `cos^2 (n x + u_n)` as `(1 + cos (2 (n x + u_n))) / 2`, identifies the constant integral with `m(E) / 2`, and finishes by showing the oscillatory term tends to zero. The prover should use `Real.tendsto_integral_exp_smul_cocompact` or a derived interval version, indicator/set-integral conversion, `Real.cos_add` plus double-angle identities, finite-measure facts from `E ⊆ Set.Icc 0 (2 * Real.pi)`, and Tendsto arithmetic.
- Complete source proof text:

```text
First, note that $\int_0^{2\pi} f(x) \cos(nx) dx \to 0$ and $\int_0^{2\pi} f(x) \sin(nx) \to 0$ since these are the real and imaginary parts of $\int_0^{2\pi} f(x) e^{-inx} dx$. In particular, if we let $f(x) = \chi_E(x)$ for some measurable $E \subset [0, 2\pi]$, then for any $\epsilon > 0$, $\exists N$ such that $\left| \int_0^{2\pi} \chi_E(x) \sin(nx) dx \right|$ and $\left| \int_0^{2\pi} \chi_E(x) \cos(nx) dx \right|$ are both less than $\frac{\epsilon}{2}$ provided $|n| > N$. Then for any sequence $u_n$,
\begin{align*}
\left| \int_E \cos(2nx + 2u_n) dx \right| &= \left| \int_E \cos(2nx) \cos(2u_n) - \sin(2nx) \sin(2u_n) dx \right| \\
&= \left| \cos(2u_n) \int_0^{2\pi} \chi_E(x) \cos(2nx) dx - \sin(2u_n) \int_0^{2\pi} \chi_E(x) \sin(2nx) dx \right| \\
&\le |\cos(2u_n)| \left| \int_0^{2\pi} \chi_E(x) \cos(2nx) dx \right| + |\sin(2u_n)| \left| \int_0^{2\pi} \chi_E(x) \sin(2nx) dx \right| \\
&\le 1 \cdot \frac{\epsilon}{2} + 1 \cdot \frac{\epsilon}{2} = \epsilon
\end{align*}
for $|n| > N$. Hence $\int_E \cos(2nx + 2u_n) dx \to 0$ as $|n| \to \infty$. Now
\begin{align*}
\int_E \cos^2(nx + u_n) dx &= \int_E \frac{1}{2} (1 + \cos(2(nx + u_n))) dx \\
&= \frac{m(E)}{2} + \frac{1}{2} \int_0^{2\pi} \chi_E(x) \cos(2nx + 2u_n) dx
\end{align*}
and we have shown that the second term tends to $0$ as $|n| \to \infty$. \qed
```

## Draft Lean Statement

```lean
theorem integral_cos_sq_tendsto_half_measure :
  (∀ f : ℝ → ℂ, IntervalIntegrable f volume 0 (2 * Real.pi) →
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ |n| →
      ‖∫ x in (0)..(2 * Real.pi), f x * Complex.exp (-Complex.I * (n : ℂ) * (x : ℂ))‖ < ε) ∧
  (∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc 0 (2 * Real.pi) →
    ∀ u : ℕ → ℝ,
      Filter.Tendsto (fun n : ℕ => ∫ x in E, (Real.cos ((n : ℝ) * x + u n)) ^ 2)
        Filter.atTop (𝓝 ((volume E).toReal / 2)))
```

## Proof-Ready Checklist

- [x] Source document inspected with `formalization_document_inspect`.
- [x] Companion instructions and candidate skeletons read and compared.
- [x] Source statement inventory entry `line-17` created with qualifiers, coverage, scope changes, source proof, and prover notes.
- [x] Root project module imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Proof queue may start after independent review approves or corrects the statement.
