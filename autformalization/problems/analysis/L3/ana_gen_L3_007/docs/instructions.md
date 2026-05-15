# ShadowBench Instructions: `analysis/L3/ana_gen_L3_007`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib
```

## Expected Declaration Names

- `diagonal_compact_iff_tendsto_zero`

## Formalization Rules

```text
open Filter
open scoped Topology

/-
Formalize in Lean the Theorem (diagonal_compact_iff_tendsto_zero) from Text.

The theorem must be named `diagonal_compact_iff_tendsto_zero`.
   Matched text (candidate 0, theorem, label=diagonal_compact_iff_tendsto_zero): \begin{theorem}[diagonal_compact_iff_tendsto_zero] Suppose $T$ is a bounded operator on a
                                                                                 Hilbert space $\mathcal{H}$ which is diagonal with respect to an orthonormal basis
                                                                                 $\{\varphi_k\}_{k=1}^{\infty}$, that is, \[ T\varphi_k = \lambda_k \varphi_k . \] Then $T$
                                                                                 is compact if and only if $\lambda_k \to 0$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
