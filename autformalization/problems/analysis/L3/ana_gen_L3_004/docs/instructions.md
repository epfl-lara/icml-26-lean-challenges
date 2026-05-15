# ShadowBench Instructions: `analysis/L3/ana_gen_L3_004`

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

- `T_spectrum`

## Formalization Rules

```text
open MeasureTheory

/-
Formalize in Lean the Theorem (T_spectrum) from Text.

The theorem must be named `T_spectrum`.
   Matched text (candidate 0, theorem, label=T_spectrum): \begin{theorem}[T_spectrum] Consider the \textit{Volterra integral operator} $T : L^2([0,
                                                          1]) \to L^2([0, 1])$ defined by: \begin{equation*} (Tf)(x) = \int_0^x f(y) \, dy, \quad x
                                                          \in [0, 1] \end{equation*} \begin{enumerate} \item Prove that $T$ is a \textbf{compact
                                                          operator}. \item Prove that the \textbf{spectrum} of $T$ consists of only the origin, i.e.,
                                                          $\sigma(T) = \{0\}$. \end{enumerate} \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
