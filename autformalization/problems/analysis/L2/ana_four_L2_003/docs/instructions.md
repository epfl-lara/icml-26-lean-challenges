# ShadowBench Instructions: `analysis/L2/ana_four_L2_003`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
```

## Expected Declaration Names

- `tendsto_integral_gaussian_smul`

## Formalization Rules

```text
open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

/-
Formalize in Lean the Lemma (tendsto_integral_gaussian_smul) from Text.

The lemma must be named `tendsto_integral_gaussian_smul`.
   Matched text (candidate 0, theorem, label=tendsto_integral_gaussian_smul): \begin{theorem}[tendsto_integral_gaussian_smul] Suppose that $f\in L^{1}(V;E)$ and $f$ is
                                                                              continuous at $v\in V$. Then we have: \[ \lim_{c\to\infty} \int_{w\in V} \Bigl((\pi
                                                                              c)^{\frac{\dim_{\mathbb R}V}{2}}\; e^{-\pi^{2}c\,\|v-w\|^{2}}\Bigr)\, f(w)\,d\mu(w) = f(v),
                                                                              \] under the hypotheses that $f$ is integrable and continuous at $v$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
