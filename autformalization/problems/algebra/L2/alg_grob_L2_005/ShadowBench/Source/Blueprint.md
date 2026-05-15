# Formalization Blueprint: `algebra/L2/alg_grob_L2_005`

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

- `maxm_coe_maxm'`
- `lm_coe_lm'`
- `coeff_zero_of_lt_lm`

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

1. Lemma (maxm_coe_maxm')
   The lemma must be named `maxm_coe_maxm'`.
   Matched text (candidate 0, paragraph): Lemma (Cox, IVA, Ch.2, Sec.2, Definition 7)
2. Lemma (lm_coe_lm')
   The lemma must be named `lm_coe_lm'`.
   Matched text (candidate 1, paragraph): Let $f, g\in R[\sigma]$ be multivariate polynomials, where $\sigma$ is a set of variable
                                          symbols over which a monomial order $>$ is fixed, and $R$ is a commutative semiring. Assume
                                          $g \ne 0$ so that it attains a leading monomial. Given $\mathrm{LM}(g) > \mathrm{LM}(f)$,
                                          the coefficient of $\mathrm{LM}(g)$ in $f$ is zero. (Technical detail: for $f = 0$, we
                                          assume $\mathrm{LM}(f)$ as `⊥ : WithBot (σ →₀ ℕ)`.)
3. Lemma (coeff_zero_of_lt_lm)
   The lemma must be named `coeff_zero_of_lt_lm`.
   Matched text (candidate 2, paragraph): Proof) Since any coefficient of $f$ given $f = 0$ is zero, we might suppose $f \ne 0$, so
                                          that $f$ also attains a leading monomial. Thanks to the assumption $\mathrm{LM}(g) >
                                          \mathrm{LM}(f)$, any monomial $x^\alpha$ with nonzero coefficient in $f$ satisfies
                                          $\mathrm{LM}(g) > \mathrm{LM}(f) \ge x^\alpha$. Therefore, none of such $x^\alpha$'s equals
                                          $\mathrm{LM}(g)$, meaning that the coefficient of $\mathrm{LM}(g)$ in…

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
