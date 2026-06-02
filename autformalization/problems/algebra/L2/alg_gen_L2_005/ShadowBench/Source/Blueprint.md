# Formalization Blueprint: `algebra/L2/alg_gen_L2_005`

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
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span
```

## Required Names

- `S`
- `zeroLocus_nonempty_of_disjoint_noZeros`

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
/-
Formalize in Lean the following named items from the theorem in the text.

1. Definition (S)
   The definition must be named `S`.
   Matched text (candidate 0, definition):
Let $S$ be the subset of all polynomials in $k[x_1,\dots,x_n]$ that have no zeros in $k^n$.

2. Theorem (zeroLocus_nonempty_of_disjoint_noZeros)
   The theorem must be named `zeroLocus_nonempty_of_disjoint_noZeros`.
   Matched text (candidate 0, theorem):
\begin{theorem}
Let $k$ be an arbitrary field and let $S$ be the subset of all polynomials in $k[x_1,\dots,x_n]$
that have no zeros in $k^n$. If $I$ is any ideal in $k[x_1,\dots,x_n]$ such that
$I \cap S=\varnothing$, then $\mathbf V(I)\neq\varnothing$.
\end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
