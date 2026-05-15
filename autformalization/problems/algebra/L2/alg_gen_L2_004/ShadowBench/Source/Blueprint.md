# Formalization Blueprint: `algebra/L2/alg_gen_L2_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz
```

## Required Names

- `exists_mem_vanishingIdeal_zeroLocus_not_mem_J`

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
Formalize in Lean the Exercise (Ch. 4 §1, Ex. 2) from Text.

The theorem must be named `exists_mem_vanishingIdeal_zeroLocus_not_mem_J`.

Matched text:
\begin{exercise}[Ch.\ 4 \S1, Ex.\ 2]
Let $J=\langle x^2+y^2-1,\ y-1\rangle$. Find $f\in \mathbf I(\mathbf V(J))$
such that $f\notin J$.
\end{exercise}
-/
```
