# ShadowBench Instructions: `algebra/L2/alg_gen_L2_030`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib
import ABM.Cox.Cox_Chapter4.Cox_Chapter4_Section3
```

## Expected Declaration Names

- `isCoprime_iff_zeroLocus_inter_eq_empty`
- `mul_eq_inf_of_isCoprime`

## Formalization Rules

```text
open MvPolynomial

/-
Formalize in Lean the two named statements from the theorem in the text.

The Lean declarations must be named exactly:
- `isCoprime_iff_zeroLocus_inter_eq_empty`
- `mul_eq_inf_of_isCoprime`

Matched text (candidate 0, theorem, label=Ch.\ 4 \S 3, Exercise 11):
\begin{theorem}[Ch.\ 4 \S 3, Exercise 11]
Two ideals $I$ and $J$ of $k[x_1,\ldots,x_n]$ are said to be \emph{coprime}
if and only if $I+J = k[x_1,\ldots,x_n]$. Show the following:
\begin{enumerate}
  \item If $k=\mathbb C$, then $I$ and $J$ are coprime if and only if
  $\mathbf V(I)\cap \mathbf V(J)=\varnothing$.
  \item If $I$ and $J$ are coprime, then $IJ = I\cap J$.
\end{enumerate}
\end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
