# Formalization Blueprint: `analysis/L2/ana_gen_L2_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
```

## Required Names

- `ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open Set MeasureTheory

/-
Formalize in Lean the Theorem (ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv) from Text.

The theorem must be named `ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv`.
   Matched text (candidate 0, theorem, label=ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv): \begin{theorem}[ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv]
                                                                                                                     Suppose that $F$ is continuous on $[a,b]$, $F'(x)$ exists for every $x \in (a,b)$, and
                                                                                                                     $F'(x)$ is integrable. Then $F$ is absolutely continuous and \[ F(b) - F(a) = \int_a^b
                                                                                                                     F'(x)\,dx. \] \end{theorem}
-/
```
