# Formalization Blueprint: `algebra/L2/alg_grob_L2_005`

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

- `coeff_zero_of_lt_lm`

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
Formalize in Lean the Lemma (coeff_zero_of_lt_lm) from Text.

The lemma must be named `coeff_zero_of_lt_lm`.
   Matched text (candidate 0, lemma, label=coeff_zero_of_lt_lm): Lemma (coeff_zero_of_lt_lm) Let $f, g\in R[\sigma]$ be multivariate polynomials, where
                                                                 $\sigma$ is a set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a
                                                                 commutative semiring. Assume $g \ne 0$ so that it attains a leading monomial. Given
                                                                 $\mathrm{LM}(g) > \mathrm{LM}(f)$, the coefficient of $\mathrm{LM}(g)$ in $f$ is zero.
                                                                 (Technical detail: for $f = 0$, we assume $\mathrm{LM}(f)$ as `⊥ : W…
-/
```
