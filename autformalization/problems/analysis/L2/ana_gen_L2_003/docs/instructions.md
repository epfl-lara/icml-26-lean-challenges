# ShadowBench Instructions: `analysis/L2/ana_gen_L2_003`

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
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
```

## Expected Declaration Names

- `saddle_sections_hasFDerivAt_eq_zero`

## Formalization Rules

```text
/-
Formalize in Lean the Theorem (saddle_sections_hasFDerivAt_eq_zero) from Text.

The theorem must be named `saddle_sections_hasFDerivAt_eq_zero`.
   Matched text (candidate 0, theorem, label=saddle_sections_hasFDerivAt_eq_zero): \begin{theorem}[saddle_sections_hasFDerivAt_eq_zero] Suppose $f : \mathbb{R}^n \times
                                                                                   \mathbb{R}^m \to \mathbb{R}$ satisfies the \textit{saddle-point property} at $(\tilde{x},
                                                                                   \tilde{z})$: for all $x \in \mathbb{R}^n$ and $z \in \mathbb{R}^m$, \[ f(\tilde{x}, z) \le
                                                                                   f(\tilde{x}, \tilde{z}) \le f(x, \tilde{z}). \] If the $x$-section $x \mapsto f(x,
                                                                                   \tilde{z})$ is differentiable at $\tilde{x}$, and the $z$-section $z…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
