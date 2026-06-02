# ShadowBench Instructions: `analysis/L2/ana_four_L2_002`

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

- `ABM_analysis_L2_ana_four_L2_002_item_1`
- `tendsto_integral_cexp_sq_smul`

## Formalization Rules

```text
open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

/-
Formalize in Lean the following named items from Text.

1. Lemma (ABM_analysis_L2_ana_four_L2_002_item_1)
   The lemma must be named `ABM_analysis_L2_ana_four_L2_002_item_1`.
   Matched text (candidate 0, lemma): \begin{lemma} Let $V$ be a finite-dimensional real inner product space, equipped with its
                                      Borel $\sigma$-algebra and a measure $dv$. Let $E$ be a complex normed vector space (assumed
                                      complete when needed), and let $f : V \to E$. We write the Fourier transform and inverse
                                      Fourier transform as follows: \[ (\mathcal{F}f)(w) \;=\; \int_V e^{-2\pi i \langle
                                      w,x\rangle}\, f(x)\,dx, \qquad (\mathcal{F}^{-}g)(v) \;=\; \int_…
2. Lemma (tendsto_integral_cexp_sq_smul)
   The lemma must be named `tendsto_integral_cexp_sq_smul`.
   Matched text (candidate 1, theorem, label=tendsto_integral_cexp_sq_smul): \begin{theorem}[tendsto_integral_cexp_sq_smul] If $f$ is integrable, then as $c$ tends to
                                                                             infinity, \[ \int_V e^{-c^{-1}\|v\|^2}\, f(v)\,dv \;\xrightarrow{}\; \int_V f(v)\,dv . \]
                                                                             \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
