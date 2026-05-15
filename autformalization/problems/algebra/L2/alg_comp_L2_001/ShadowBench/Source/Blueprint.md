# Formalization Blueprint: `algebra/L2/alg_comp_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.MonomialOrder
```

## Required Names

- `expSet`

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
open scoped MonomialOrder

/-
Formalize in Lean the Definition (expSet) from Text.

The definition must be named `expSet`.
   Matched text (candidate 0, definition, label=expSet): \begin{definition}[expSet] Suppose that $I = \langle x^\alpha \mid \alpha \in A \rangle$ is
                                                         a monomial ideal, and let $S$ be the set of all exponents that occur as monomials of $I$.
                                                         For any monomial order $>$, prove that the smallest element of $S$ with respect to $>$ must
                                                         lie in $A$. \end{definition}
-/
```
