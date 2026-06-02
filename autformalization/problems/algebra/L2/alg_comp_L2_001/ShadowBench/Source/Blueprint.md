# Formalization Blueprint: `algebra/L2/alg_comp_L2_001`

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
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.MonomialOrder
```

## Required Names

- `minimal_monomial_mem_generators`

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
open MvPolynomial
open scoped MonomialOrder

/-
Formalize in Lean the named statement from the theorem in the text.

The Lean declaration must be named exactly:
- `minimal_monomial_mem_generators`

Matched text (candidate 0, theorem):
\begin{theorem}
Suppose that $I = \langle x^\alpha \mid \alpha \in A \rangle$ is a monomial ideal,
and let $S$ be the set of all exponents that occur as monomials of $I$.
Then, for any monomial order $>$, prove that the smallest element of $S$ with respect to $>$
must lie in $A$.
\end{theorem}
-/
```
