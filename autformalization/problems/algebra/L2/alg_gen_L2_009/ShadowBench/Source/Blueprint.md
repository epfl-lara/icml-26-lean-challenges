# Formalization Blueprint: `algebra/L2/alg_gen_L2_009`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.AdjoinRoot
```

## Required Names

- `J`

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
open scoped BigOperators
open MvPolynomial

/-
Formalize in Lean the Definition (J) from Text.

The definition must be named `J`.
   Matched text (candidate 0, definition, label=J): \begin{definition}[J] Let $k$ be an arbitrary field and let $I,J$ be ideals in
                                                    $k[x_1,\ldots,x_n]$. Show the following: \begin{enumerate} \item $\sqrt{IJ} = \sqrt{I \cap
                                                    J}$. \item In $k[x,y]$, let $I=\langle x\rangle$ and $J=\langle x,y\rangle$. Show that $I$
                                                    and $J$ are radical ideals, but $IJ$ is not a radical ideal. \item In $k[x,y]$, with
                                                    $I=\langle x\rangle$ and $J=\langle x,y\rangle$ as above, show that $\sqr…
-/
```
