# Formalization Blueprint: `analysis/L2/ana_four_L2_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source and support files inspected

- `docs/source.tex`: one theorem-like block, source inventory label `line-17`, a lemma named `tendsto_integral_gaussian_smul`.
- `.epflemma/workflow-state/formalization/docs-source/manifest.json`: confirms source kind `latex`, no citations, no bibliography files, and no additional PDF support files.
- `.epflemma/workflow-state/formalization/docs-source/context.md`: workflow contract and preflight source excerpt.
- `docs/instructions.md`: required declaration name `tendsto_integral_gaussian_smul`; starting imports are `Mathlib.MeasureTheory.Integral.PeakFunction` and `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`.
- `docs/skeletons/README.md` and `docs/skeletons/Skeleton1.lean` through `Skeleton4.lean`: all suggest the same basic declaration shape; `Skeleton4.lean` is syntactically malformed by an extra `:= by sorry`, and all skeletons use an arbitrary measure parameter in a way that is not justified by the Gaussian normalization proof.

No project-local PDF was listed in the manifest or found among `docs/` support files, so no `read_pdf` pass was needed.

## Import Plan

```lean
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
```

These are the direct imports currently used by `ShadowBench/Source/Main.lean`. They match the allowed starting imports from `docs/instructions.md` and are sufficient for the drafted statement. If a later proof uses the already-proved Mathlib convergence theorem, the prover may add `Mathlib.Analysis.Fourier.Inversion` and update this plan.

## Suggested Search Modules

- `Mathlib.MeasureTheory.Integral.PeakFunction`: approximate-identity theorem `MeasureTheory.tendsto_integral_comp_smul_smul_of_integrable'`, matching the source proof.
- `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`: Gaussian integral lemma `GaussianFourier.integral_rexp_neg_mul_sq_norm`.
- `Mathlib.Analysis.Fourier.Inversion`: nearby Mathlib theorem `Real.tendsto_integral_gaussian_smul'`, a complex-valued version of this Gaussian point-evaluation limit.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed declaration `tendsto_integral_gaussian_smul` with a `by sorry` proof stub for the later prover queue.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

The root project module already imports the generated target module path, so plain project verification covers `ShadowBench/Source/Main.lean`.

## Required Names

- `tendsto_integral_gaussian_smul`

## Source Statement Inventory

### line-17

- Source title: lemma `tendsto_integral_gaussian_smul`.
- Planned Lean declarations: `tendsto_integral_gaussian_smul` in `ShadowBench/Source/Main.lean`.
- Source locator: `line-17` (`docs/source.tex`, lemma statement lines 17--26; proof lines 28--86).
- Skeleton candidate used: `Skeleton1.lean`/`Skeleton2.lean`/`Skeleton3.lean` shaped the name, basic variables, hypotheses `Integrable f` and `ContinuousAt f v`, and `Tendsto ... atTop (𝓝 (f v))`; the final statement corrects the skeletons by placing the whole real Gaussian coefficient inside the integrand as a real scalar action and by using Lean's default volume measure rather than an unsupported arbitrary measure parameter. `Skeleton4.lean` was not adopted because it has a duplicated proof terminator.
- Dependencies for the statement: `Filter.Tendsto`, `MeasureTheory.Integrable`, Bochner integral notation, `ContinuousAt`, `finrank ℝ V`, finite-dimensional real inner product space structure, real normed complete target space, `Real.pi`, `Real.exp`, and real scalar multiplication.
- Dependencies suggested for the proof: construct `φ w = π ^ ((finrank ℝ V : ℝ) / 2) * Real.exp (-(π ^ 2) * ‖w‖ ^ 2)`, prove positivity/integral-one/decay via `GaussianFourier.integral_rexp_neg_mul_sq_norm` and exponential decay lemmas, apply `MeasureTheory.tendsto_integral_comp_smul_smul_of_integrable'`, then substitute `c ↦ c ^ (1/2)` as in the source. Alternatively compare with `Real.tendsto_integral_gaussian_smul'` from `Mathlib.Analysis.Fourier.Inversion` after handling the real/complex scalar representation.
- Formal statement review: the drafted theorem preserves the displayed real Gaussian kernel, the `c → ∞` limit, the integrability and continuity hypotheses, and the point-evaluation conclusion. The source measure notation `dμ` is represented by Lean's canonical volume measure, because the source proof uses the normalized Gaussian integral formula.
- Source qualifiers:
  - Mathematical object class: finite-dimensional real inner product domain and complete real normed target space.
  - Quantifier order: ambient spaces and structures, then `f : V → E`, `v : V`, `Integrable f`, and `ContinuousAt f v`.
  - Parameter domain: `c : ℝ` tends to `+∞` along `atTop`, so the positive-`c` kernel simplifications are eventual facts.
  - Output codomain: convergence in `E` to `f v`.
  - Equality/image condition: the Bochner integral of the Gaussian-weighted function tends to point evaluation.
  - Side conditions: integrability and continuity at `v`, finite-dimensionality over `ℝ`, and canonical normalized Haar/Lebesgue measure.
  - Follow-on statement claims: none beyond the displayed convergence/equality; the normalized-Gaussian integral-one, nonnegativity, concentration, and exponential-decay facts occur in the proof and are recorded as proof dependencies/prover notes rather than extra theorem conclusions.
- Lean coverage: complete for the source-supported canonical Haar/Lebesgue measure interpretation recorded under `Scope changes`; `dim_ℝ V` is `finrank ℝ V`, `f ∈ L¹(V;E)` is `Integrable f`, continuity is `ContinuousAt f v`, and the displayed kernel is represented by real scalar multiplication inside the Bochner integral.
- Scope changes: the skeletons' arbitrary `μ : Measure V` is not retained. The source writes `dμ` but gives no arbitrary-measure hypotheses and its proof invokes the standard Gaussian integral formula, so this review treats `μ` as the canonical Haar/Lebesgue `volume` measure. This is a recorded notation/representation choice, not coverage of an arbitrary named measure.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: recorded below.
- Source proof / prover notes: use the approximate-identity proof recorded below; instantiate `MeasureTheory.tendsto_integral_comp_smul_smul_of_integrable'` with the fixed Gaussian and compose with `c ↦ c ^ (1 / 2 : ℝ)`.

#### Source statement

Suppose that $f \in L^{1}(V;E)$ and $f$ is continuous at $v \in V$. Then
\[
\lim_{c\to\infty}
\int_{w\in V}
\Bigl((\pi c)^{\frac{\dim_{\mathbb R}V}{2}}
 e^{-\pi^{2}c\,\|v-w\|^{2}}\Bigr)\, f(w)\,d\mu(w)
= f(v),
\]
under the hypotheses that $f$ is integrable and continuous at $v$.

#### Source proof text

Define the fixed Gaussian
\[
\varphi(w) := \pi^{\frac n2} e^{-\pi^2 \|w\|^2},
\qquad w \in V.
\]
Consider the family of kernels
\[
K_c(w) := c^n\, \varphi(c w), \qquad c > 0.
\]
Then
\[
\int_V K_c(w)\, d\mu(w)
=
\int_V c^n \varphi(c w)\, d\mu(w)
= 1,
\]
by the standard Gaussian integral formula. Moreover, $K_c \ge 0$ and the family $\{K_c\}_{c>0}$ concentrates at the origin: for any $\varepsilon>0$,
\[
\int_{\|w\|>\varepsilon} K_c(w)\, d\mu(w) \longrightarrow 0
\qquad (c\to\infty),
\]
since $\varphi$ has exponential decay and $t^{\alpha} e^{-t} \to 0$ as $t \to \infty$ for any $\alpha>0$.

By the standard approximate identity theorem, using the integrability of $f$ and continuity of $f$ at $v$, we obtain
\[
\lim_{c \to \infty}
\int_V c^n \varphi\bigl(c(v-w)\bigr)\, f(w)\, d\mu(w)
= f(v).
\]
Replacing $c$ by $c^{1/2}$ yields
\[
\lim_{c \to \infty}
\int_V (c^{1/2})^n \varphi\bigl((c^{1/2})(v-w)\bigr)\, f(w)\, d\mu(w)
= f(v).
\]
For $c>0$ and all $w\in V$,
\[
(c^{1/2})^n \varphi\bigl((c^{1/2})(v-w)\bigr)
=
\pi^{\frac n2} c^{\frac n2}
\exp\!\bigl(-\pi^2 \|(c^{1/2})(v-w)\|^2\bigr).
\]
Since $\|(c^{1/2})(v-w)\|^2 = c\,\|v-w\|^2$, this simplifies to
\[
(\pi c)^{\frac n2} e^{-\pi^2 c \|v-w\|^2}.
\]
Therefore, for all sufficiently large $c$, the integrand in ($\dagger$) coincides with the integrand in the statement. Hence,
\[
\lim_{c \to \infty}
\int_V
(\pi c)^{\frac n2} e^{-\pi^2 c \|v-w\|^2}\, f(w)\, d\mu(w)
= f(v).
\]

#### Source qualifiers

- Mathematical object class: finite-dimensional real normed/vector space with the Euclidean/inner-product structure needed for `‖v-w‖`, Gaussian integral normalization, and `dim_ℝ V`; target `E` is a complete real normed vector space for Bochner integration.
- Quantifier order: choose `V`, `E`, structures, then `f : V → E`, `v : V`, integrability of `f`, and continuity of `f` at `v`.
- Parameter domain: real parameter `c` tends to `+∞`; the displayed kernel is eventually evaluated for positive `c`.
- Output codomain: convergence in the topology of `E` to `f v`.
- Equality/image condition: the limit of the Bochner integral of the Gaussian-weighted function equals point evaluation.
- Side conditions: `f` is integrable and continuous at `v`; `V` is finite-dimensional over `ℝ`; measure is the canonical normalized Haar/Lebesgue measure implicit in the Gaussian integral formula.
- Follow-on statement claims: none beyond the displayed convergence/equality. The proof uses that the normalized Gaussian has integral one, is nonnegative, decays at infinity, and its dilations form an approximate identity; these are proof dependencies rather than extra theorem conclusions.

#### Lean coverage

The Lean theorem states the real-valued Gaussian kernel exactly as
`((Real.pi * c) ^ ((finrank ℝ V : ℝ) / 2)) * Real.exp (-(Real.pi ^ 2) * c * ‖v - w‖ ^ 2)` acting by real scalar multiplication on `f w`, integrated over `w : V`, and tending along `atTop` to `f v`. The source dimension `dim_ℝ V` is represented by `finrank ℝ V`. The source hypotheses `f ∈ L¹(V;E)` and continuity at `v` are represented by `Integrable f` and `ContinuousAt f v`. This covers the source statement for the canonical Haar/Lebesgue measure interpretation described under `Scope changes`; it does not assert an arbitrary-measure version.

#### Scope changes

The source writes `dμ(w)` but does not separately state assumptions on `μ`. Because the proof invokes the standard normalized Gaussian integral formula, this review interprets `μ` as Lean's default Haar/Lebesgue measure `volume` on a finite-dimensional real inner product space. The skeletons' unconstrained arbitrary `μ : Measure V` version is not valid as stated and is intentionally omitted; if a future review requires an arbitrary named measure reading, the Lean statement must be revised with a normalization/volume bridge assumption before proof handoff.

#### Formal statement review

The drafted Lean statement preserves the displayed kernel, the `c → ∞` limit, the integrability and continuity hypotheses, and the point-evaluation conclusion. The only deliberate representation bridge is the treatment of `dμ` as the canonical volume measure, recorded above.

#### Statement verification status

PASS. 2026-06-05 statement-fidelity review confirmed the Lean kernel `(π c)^(finrank ℝ V/2) · exp(-π² c ‖v-w‖²)`, hypotheses `Integrable f` and `ContinuousAt f v`, and the `atTop → 𝓝 (f v)` conclusion match the source; `volume` is the recorded measure bridge. Lean check passes (sorry-only).

#### Prover notes

Use the source approximate-identity proof. The key Mathlib theorem for the proof is `MeasureTheory.tendsto_integral_comp_smul_smul_of_integrable'`. Instantiate it with the fixed Gaussian `φ`, verify `∫ φ = 1` using `GaussianFourier.integral_rexp_neg_mul_sq_norm`, prove decay via exponential decay/rpow lemmas, apply it to `f` at `v`, then compose with `fun c ↦ c ^ (1 / 2 : ℝ)` and simplify the kernel. Searching `Real.tendsto_integral_gaussian_smul'` in `Mathlib.Analysis.Fourier.Inversion` gives a nearby already-proved complex-valued version of the same convergence.

## Draft checklist

- [x] Source document and preflight manifest inspected.
- [x] Project instructions and skeleton files inspected.
- [x] Local/Mathlib search performed before choosing the final declaration shape.
- [x] Blueprint source map updated with source locator, declaration name, dependencies, statement-fidelity notes, complete source proof text, and prover notes.
- [x] Root project module imports the generated target module through `ShadowBench.lean` → `ShadowBench/Source.lean` → `ShadowBench/Source/Main.lean`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
