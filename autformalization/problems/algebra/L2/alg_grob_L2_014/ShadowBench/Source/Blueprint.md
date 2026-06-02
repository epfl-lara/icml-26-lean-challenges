# Formalization Blueprint: `algebra/L2/alg_grob_L2_014`

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

- `lm_sum_le_of_all_lm_le`

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
Formalize in Lean the Lemma (lm_sum_le_of_all_lm_le) from Text.

The lemma must be named `lm_sum_le_of_all_lm_le`.
   Matched text (candidate 0, lemma, label=lm_sum_le_of_all_lm_le): Lemma (lm_sum_le_of_all_lm_le) Upper bound of the leading monomial of finite sum Let $f_1,
                                                                    f_2, \cdots, f_n \in R[\sigma]$ be multivariate polynomials (which might be zero). Here,
                                                                    $\sigma$ is a set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a
                                                                    nontrivial commutative semiring. Given a monomial $x^\delta$ such that $\mathrm{LM}(f_i) \le
                                                                    x^\delta$ for every $i = 1, 2, \cdots, n$, we have $\…
-/
```
