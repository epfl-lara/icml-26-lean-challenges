# Formalization Blueprint: `algebra/L2/alg_grob_L2_014`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
```

## Required Names

- `lm_add_le_of_both_lm_le`
- `lm_add_le_of_both_lm_le_mon`
- `lm_sum_le_of_all_lm_le`

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
/-
Formalize in Lean the following named items from Text.

1. Lemma (lm_add_le_of_both_lm_le)
   The lemma must be named `lm_add_le_of_both_lm_le`.
   Matched text (candidate 0, paragraph): Lemma (Cox, IVA, Ch.2, Sec.2, Lemma 8; generalization) Upper bound of the leading monomial
                                          of finite sum
2. Lemma (lm_add_le_of_both_lm_le_mon)
   The lemma must be named `lm_add_le_of_both_lm_le_mon`.
   Matched text (candidate 1, paragraph): Let $f_1, f_2, \cdots, f_n \in R[\sigma]$ be multivariate polynomials (which might be zero).
                                          Here, $\sigma$ is a set of variable symbols over which a monomial order $>$ is fixed, and
                                          $R$ is a nontrivial commutative semiring. Given a monomial $x^\delta$ such that
                                          $\mathrm{LM}(f_i) \le x^\delta$ for every $i = 1, 2, \cdots, n$, we have
                                          $\mathrm{LM}(\sum_{i=1}^n f_i) \le x^\delta$.
3. Lemma (lm_sum_le_of_all_lm_le)
   The lemma must be named `lm_sum_le_of_all_lm_le`.
   Matched text (candidate 2, paragraph): Proof) Induction on $n$, with initial case $n = 1$ assumed and $n = 2$ already proven,
                                          directly gives the conclusion.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
