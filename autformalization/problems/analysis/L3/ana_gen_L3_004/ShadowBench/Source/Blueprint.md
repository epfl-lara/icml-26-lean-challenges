# Formalization Blueprint: `analysis/L3/ana_gen_L3_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `T_spectrum`

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
