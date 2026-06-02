# Formalization Blueprint: `algebra/L2/alg_gen_L2_017`

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
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
```

## Required Names

- `MvPolynomial.monomialIdeal`
- `MonomialOrder.mem_monomialIdeal_iff_divisible`

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
Formalize in Lean the following named items from the lemma in the text.

1. Definition (monomialIdeal)
   The definition must be named `MvPolynomial.monomialIdeal`.
   Matched text (candidate 0, definition):
Let $I = \langle x^\alpha \mid \alpha \in A \rangle$ be a monomial ideal.

2. Lemma (mem_monomialIdeal_iff_divisible)
   The lemma must be named `MonomialOrder.mem_monomialIdeal_iff_divisible`.
   Matched text (candidate 0, lemma, label=mem_monomialIdeal_iff_divisible):
\begin{lemma}[mem_monomialIdeal_iff_divisible]\label{lem:mem_monomialIdeal_iff_divisible}
    Let $I = \langle x^\alpha \mid \alpha \in A \rangle$ be a monomial ideal.
    Then a monomial $x^\beta$ lies in $I$ if and only if $x^\beta$ is divisible by
    $x^\alpha$ for some $\alpha \in A$.
\end{lemma}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
