# Formalization Blueprint: `algebra/L2/alg_gen_L2_030`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
import ABM.Cox.Cox_Chapter4.Cox_Chapter4_Section3
```

## Required Names

- `isCoprime_iff_zeroLocus_inter_eq_empty`
- `mul_eq_inf_of_isCoprime`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

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
