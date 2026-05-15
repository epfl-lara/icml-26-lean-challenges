# Formalization Blueprint: `algebra/L2/alg_grob_L2_015`

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

- `max_monomial'`
- `leading_monomial'`
- `lm'_add_lt_of_both_lm'_lt`

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

1. Definition (max_monomial')
   The definition must be named `max_monomial'`.
   Matched text (candidate 0, paragraph): Lemma (Cox, IVA, Ch.2, Sec.2, Lemma 8; less-than version) Leading monomial of addition
                                          (nonzero case)
2. Definition (leading_monomial')
   The definition must be named `leading_monomial'`.
   Matched text (candidate 1, paragraph): Let $f_1, f_2, g \in R[\sigma]$ be nonzero multivariate polynomials, and suppose that the
                                          sum $f_1 + f_2$ is also nonzero. Here, $\sigma$ is a set of variable symbols over which a
                                          monomial order $>$ is fixed, and $R$ is a commutative semiring. Given $\mathrm{LM}(f_1) <
                                          \mathrm{LM}(g)$ and $\mathrm{LM}(f_2) < \mathrm{LM}(g)$, we have $\mathrm{LM}(f_1 + f_2) <
                                          \mathrm{LM}(g)$.
3. Lemma (lm'_add_lt_of_both_lm'_lt)
   The lemma must be named `lm'_add_lt_of_both_lm'_lt`.
   Matched text (candidate 2, paragraph): Proof) It is assumed that every monomial in $f_1$ or $f_2$ is less than $\mathrm{LM}(g)$,
                                          under the fixed monomial order. Since the monomials in $f_1 + f_2$ must be in at least one
                                          of $f_1$ and $f_2$, those monomials must still be less than $\mathrm{LM}(g)$, hence the
                                          inequality.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
