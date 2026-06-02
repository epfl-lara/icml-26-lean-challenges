# Formalization Blueprint: `algebra/L2/alg_grob_L2_013`

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
import Mathlib.Data.Finsupp.MonomialOrder
```

## Required Names

- `lm_add_le_of_both_lm_le_mon`

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
Formalize in Lean the Lemma (lm_add_le_of_both_lm_le_mon) from Text.

The lemma must be named `lm_add_le_of_both_lm_le_mon`.
   Matched text (candidate 0, lemma, label=lm_add_le_of_both_lm_le_mon): Lemma (lm_add_le_of_both_lm_le_mon) Upper bound of the leading monomial of addition Let
                                                                         $f_1, f_2 \in R[\sigma]$ be multivariate polynomials (which might be zero). Here, $\sigma$
                                                                         is a set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a
                                                                         nontrivial commutative semiring. Given a monomial $x^\delta$ such that $\mathrm{LM}(f_1) \le
                                                                         x^\delta$ and $\mathrm{LM}(f_2) \le x^\delta$, we have $\mathrm…
-/
```
