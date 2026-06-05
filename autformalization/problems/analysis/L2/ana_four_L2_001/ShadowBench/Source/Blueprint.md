# Formalization Blueprint: `analysis/L2/ana_four_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed definition `fourierIntegral` and theorem skeleton `fourierIntegral_const_smul`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target is covered by project-level `lake build`/`lean_verify(mode=project)`.

## Import Plan

Direct Lean imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
```

## Suggested Search Modules

These are search/proof hints only, not additional direct imports at this stage.

- `Mathlib.MeasureTheory.Integral.Bochner.Basic`: `MeasureTheory.integral_smul`, `MeasureTheory.Integrable.integral_smul`.
- `Mathlib.Algebra.Group.AddChar`: `AddChar` coercion/application lemmas.
- `Mathlib.Analysis.Complex.Circle`: coercion `Circle → ℂ` and multiplicative circle lemmas.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`.
- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` use `L : V × W → K` and either an underspecified `AddChar K` or an unstructured bilinear function. They capture the displayed integral shape but do not encode the source phrase “a bilinear form” as a Lean structure.
- `Skeleton4.lean` shaped the final declarations: `L : V →ₗ[K] W →ₗ[K] K` represents the bilinear form as a curried linear map, and `e : AddChar K Circle` represents the additive character into the unit circle. The final draft adds the explicit measurable-space parameter required by `Measure V`.

## Required Names

- `fourierIntegral`
- `fourierIntegral_const_smul`

## Source Statement Inventory

### line-17

- Planned Lean declarations: `fourierIntegral` (noncomputable definition).
- Source locator: `docs/source.tex`, definition environment `[fourierIntegral]`, lines 17--28.
- Source statement: Let `K` be a commutative ring and let `V, W` be modules over `K`. Let `E` be a complete normed `ℂ`-vector space, `μ` be a measure on `V`, `L : V × W → K` a bilinear form, and let `e : K → 𝕊` be an additive character. For `f : V → E`, define
  `\widehat f_{e,μ,L}(w) := ∫_V e(-L(v,w)) f(v) dμ(v)`, and set `𝓕_{e,μ,L}(f) = \widehat f_{e,μ,L}`.
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean`, with explicit `[MeasurableSpace V]` added.
- Dependencies: direct imports in `## Import Plan`; Mathlib objects `AddChar`, `Circle`, `Measure`, Bochner integral notation, `LinearMap`.
- Formal statement review: the Lean definition has parameters `{K V W E}` with `[CommRing K]`, `[MeasurableSpace V]`, `[AddCommGroup V] [Module K V]`, `[AddCommGroup W] [Module K W]`, `[NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]`, then `(μ : Measure V)`, `(L : V →ₗ[K] W →ₗ[K] K)`, `(e : AddChar K Circle)`, `(f : V → E)`, and returns `W → E` by `fun w ↦ ∫ v, ((e (-L v w) : Circle) : ℂ) • f v ∂μ`.
- Source qualifiers:
  - Mathematical object class: commutative ring `K`; `K`-modules `V,W`; complete normed complex vector space `E`; measure `μ` on `V`; bilinear form `L`; additive character `e` into the unit circle.
  - Quantifier/order context: all objects are fixed before the function `f`, and the output is a function of `w : W`.
  - Parameter domain/codomain: `f : V → E`; `fourierIntegral ... f : W → E`.
  - Equality/image condition: value at `w` is the Bochner integral of the complex scalar `e(-L(v,w))` acting on `f v`.
  - Side conditions: Lean makes the measurable space underlying `μ` explicit.
  - Follow-on claims: the notation `𝓕_{e,μ,L}(f) = \widehat f_{e,μ,L}` is represented by the Lean definition name `fourierIntegral μ L e f`, whose value is the displayed `w ↦ ...` transform.
- Lean coverage: the Lean declaration `fourierIntegral` covers the transform operator `𝓕` and the hatted function by returning `W → E`; the bilinear-form object class is encoded by the curried linear-map type `V →ₗ[K] W →ₗ[K] K`, whose application `L v w` represents the product-domain value `L(v,w)`; and `e : AddChar K Circle` is coerced through `Circle → ℂ` to act on `E` by complex scalar multiplication.
- Scope changes: representation bridge only: the source product bilinear form `V × W → K` is represented by a curried linear-map object, and the source circle `𝕊` is represented by Mathlib’s `Circle`; Lean also exposes `[MeasurableSpace V]` because `Measure V` depends on it. No mathematical weakening or strengthening is intended.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition; no proof. For theorem proofs, unfold `fourierIntegral` to recover the displayed integral.

### line-31

- Planned Lean declarations: `fourierIntegral_const_smul` (theorem; proof skeleton by sorry for the later `/prove` workflow).
- Source locator: `docs/source.tex`, theorem environment `[fourierIntegral_const_smul]`, statement lines 31--36, proof lines 36--51.
- Source statement: Let `r ∈ ℂ`. Then `𝓕_{e,μ,L}(r · f) = r · \widehat f_{e,μ,L}`.
- Complete source proof text: “We show that the two functions are equal at any `w ∈ W`.
  \[
  \begin{aligned}
  \hat{rf}_{e,\mu,L}(w)
  &= \int_V e\!\bigl(-L(v,w)\bigr)\, (r \cdot f(v))\, d\mu(v) \\
  &= r \int_V e\!\bigl(-L(v,w)\bigr)\, f(v)\, d\mu(v)
  \qquad\text{(linearity of the integral)} \\
  &= r \cdot \widehat{f}_{e,\mu,L}(w).
  \end{aligned}
  \]”
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean`, aligned with the final `fourierIntegral` representation.
- Dependencies: `fourierIntegral`; Bochner integral scalar-linearity lemma found by search as `MeasureTheory.integral_smul`; function extensionality for equality of functions.
- Formal statement review: the Lean theorem quantifies the same ambient data as `fourierIntegral` and then `(r : ℂ)`, and states
  `fourierIntegral μ L e (r • f) = r • fourierIntegral μ L e f`.
- Source qualifiers:
  - Mathematical object class: same `K,V,W,E,μ,L,e,f` context as the definition, plus `r : ℂ`.
  - Quantifier order: ambient Fourier-transform data and `f` precede the scalar `r`.
  - Parameter domain/codomain: both sides are functions `W → E`.
  - Equality/image condition: equality is a function equality, equivalently pointwise for all `w : W`.
  - Side conditions: no integrability assumption appears in the source; Lean’s Bochner integral is total, and the expected scalar-linearity theorem works at this level.
  - Follow-on claims: none beyond the displayed scalar-multiplication equality.
- Lean coverage: the Lean theorem covers the scalar-multiplication equality in the same recorded representation as `line-17`. The term `r • f` is Lean’s pointwise scalar multiplication on functions `V → E`; `r • fourierIntegral μ L e f` is pointwise scalar multiplication on functions `W → E`; equality is equality in `W → E`.
- Scope changes: same representation bridge as `line-17`; no additional theorem weakening or strengthening, domain restriction, integrability assumption, or conclusion omission is intended.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: use `funext w`; unfold `fourierIntegral`; rewrite the integrand so `((e (-L v w) : Circle) : ℂ) • (r • f v)` is `r • (((e (-L v w) : Circle) : ℂ) • f v)` using commutativity/associativity of complex scalar multiplication; then apply `MeasureTheory.integral_smul` and close by extensionality/simp.

## Formalization Rules Snapshot

```text
open MeasureTheory Filter
open scoped Topology

Formalize exactly the named items `fourierIntegral` and `fourierIntegral_const_smul` from `docs/source.tex`.
Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
During drafting, theorem/lemma/example proofs remain `by sorry` until an independent statement/source review approves the statements and a later `/prove` workflow starts.
```
