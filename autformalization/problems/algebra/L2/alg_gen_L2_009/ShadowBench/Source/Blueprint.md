# Formalization Blueprint: `algebra/L2/alg_gen_L2_009`

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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.AdjoinRoot
```

## Required Names

- `radical_mul_eq_radical_inf`
- `span_X_isRadical_and_span_X_Y_isRadical_and_mul_not_isRadical`
- `radical_mul_ne_mul_radicals_span_X_span_X_Y`

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
open scoped BigOperators
open MvPolynomial

/-
Formalize in Lean the three named statements from the theorem in the text.

The Lean declarations must be named exactly:
- `radical_mul_eq_radical_inf`
- `span_X_isRadical_and_span_X_Y_isRadical_and_mul_not_isRadical`
- `radical_mul_ne_mul_radicals_span_X_span_X_Y`

Matched text (candidate 0, theorem):
\begin{theorem}
Let $k$ be an arbitrary field and let $I,J$ be ideals in $k[x_1,\ldots,x_n]$.
Then
\begin{enumerate}
  \item $\sqrt{IJ} = \sqrt{I \cap J}$.

  \item In $k[x,y]$, let $I=\langle x\rangle$ and $J=\langle x,y\rangle$.
  Show that $I$ and $J$ are radical ideals, but $IJ$ is not a radical ideal.

  \item In $k[x,y]$, with $I=\langle x\rangle$ and $J=\langle x,y\rangle$ as above,
  show that $\sqrt{IJ} \neq \sqrt{I}\,\sqrt{J}$.
\end{enumerate}
\end{theorem}
-/
```
