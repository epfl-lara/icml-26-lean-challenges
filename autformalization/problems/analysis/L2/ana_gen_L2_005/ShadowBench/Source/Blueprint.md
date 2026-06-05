# Formalization Blueprint: `analysis/L2/ana_gen_L2_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Import Plan

Direct imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
```

## Suggested Search Modules

These are proof-search hints only, not direct imports in the draft:

- `Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun`
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable`
- `Mathlib.MeasureTheory.Integral.DominatedConvergence`

## Generated File Layout

Decision: keep the generated formalization single-file. The source has one theorem, no separate
source definitions or constructions, and the declaration count is well below the split threshold;
splitting into `Basic.lean`, `Constructions.lean`, or `Theorems.lean` would add import overhead
without improving organization.

- `ShadowBench.lean` imports `ShadowBench.Source`.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench/Source/Main.lean` contains the single source-backed theorem skeleton.
- There are no generated sibling Lean modules beyond the `Source.lean` aggregator.

## Required Names

- `ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv`

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem lines 17--22; proof environment lines 24--56.
- Source kind: theorem.
- Source title: `ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv`.
- Planned Lean declarations: `ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Formal statement review: The Lean theorem states the two source conclusions, absolute continuity of `F` on the closed interval and the endpoint integral identity, under formal versions of the three source hypotheses: continuity on `[a,b]`, derivative existence on `(a,b)`, and integrability of `F'` on the interval.
- Source qualifiers: mathematical object class is a one-variable real-valued function on a real interval; quantifier order is endpoints `a b`, function `F`, then continuity, derivative-existence, and integrability assumptions; parameter domains are `[a,b]` for continuity and absolute continuity and `(a,b)` for differentiability; output codomain is real; equality condition is `F(b) - F(a) = ∫_a^b F'(x) dx`; side condition is the usual ordered-interval convention for `[a,b]`; follow-on claims are both absolute continuity and the endpoint equality.
- Lean coverage: `{a b : ℝ} {F : ℝ → ℝ}` covers the real endpoints and real-valued function; `hcont : ContinuousOn F (Icc a b)` with `hab : a ≤ b` covers continuity on `[a,b]`; `hdiff : DifferentiableOn ℝ F (Ioo a b)` covers derivative existence on `(a,b)`; `hintegr : IntervalIntegrable (deriv F) volume a b` covers derivative integrability on the interval; `AbsolutelyContinuousOnInterval F a b` covers the absolute-continuity conclusion on the same closed interval; `F b - F a = ∫ x in a..b, deriv F x` covers the endpoint equality with source `F'` represented by `deriv F`.
- Scope changes: explicit `hab : a ≤ b` records the source convention that `[a,b]` is ordered; the implicit codomain is fixed to the standard real-valued reading `F : ℝ → ℝ`; source notation `F'` is represented by Mathlib's canonical derivative `deriv F`; the ambiguous word "integrable" is represented by Mathlib interval integrability, matching the provided skeletons and interval-integral imports.
- Skeleton candidate used: `docs/skeletons/Skeleton1.lean`--`docs/skeletons/Skeleton3.lean` for the real-valued `deriv F` / `IntervalIntegrable (deriv F)` shape and required name. `docs/skeletons/Skeleton4.lean` served only as a hint for the explicit interval-order side condition; its vector-valued codomain and separate derivative function were not adopted because the source statement uses standard scalar real-analysis notation.
- Dependencies: `ContinuousOn F (Icc a b)`, `DifferentiableOn ℝ F (Ioo a b)`, `IntervalIntegrable (deriv F) volume a b`, `AbsolutelyContinuousOnInterval F a b`; likely proof facts include `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`, closure of `AbsolutelyContinuousOnInterval` under constants and sums, and FTC lemmas from `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` such as `intervalIntegral.integral_deriv_eq_sub_uIoo`.
- Source proof text: Let \[ G(x) := F(a) + \int_a^x F'(t)\,dt . \] Then $F$ agrees with $G$ on $[a,b]$. Since $F'$ is integrable on $[a,b]$, the function \[ x\mapsto \int_a^x F'(t)\,dt \] is absolutely continuous on $[a,b]$. The constant function $x\mapsto F(a)$ is also absolutely continuous on $[a,b]$. Hence their sum $G$ is absolutely continuous on $[a,b]$. Because $F=G$ on $[a,b]$, it follows that $F$ itself is absolutely continuous on $[a,b]$. Finally, applying the fundamental theorem of calculus on the whole interval $[a,b]$, using the continuity of $F$ on $[a,b]$, differentiability on $(a,b)$, and integrability of $F'$, we obtain \[ \int_a^b F'(t)\,dt = F(b)-F(a). \] Equivalently, \[ F(b)-F(a)=\int_a^b F'(t)\,dt . \] Thus \[ F \text{ is absolutely continuous on } [a,b] \quad\text{and}\quad F(b)-F(a)=\int_a^b F'(t)\,dt . \]
- Prover notes: Follow the source primitive-comparison proof. Define `G x = F a + ∫ t in a..x, deriv F t`; use absolute continuity of interval-integral primitives plus constants and sums to prove `G` is absolutely continuous; transfer to `F` using the asserted equality on `[a,b]`; use an FTC lemma for `∫ x in a..b, deriv F x = F b - F a`. If the primitive equality is the proof bottleneck in Mathlib, return to statement/source review rather than changing this reviewed statement during proving.

#### Lean statement draft

```lean
theorem ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv
    {a b : ℝ} {F : ℝ → ℝ}
    (hcont : ContinuousOn F (Icc a b))
    (hab : a ≤ b)
    (hdiff : DifferentiableOn ℝ F (Ioo a b))
    (hintegr : IntervalIntegrable (deriv F) volume a b) :
    AbsolutelyContinuousOnInterval F a b ∧ F b - F a = ∫ x in a..b, deriv F x
```
