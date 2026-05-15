# ShadowBench Instructions: `analysis/L2/ana_gen_L2_005`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
```

## Expected Declaration Names

- `ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
