# Formalization Blueprint: `algebra/L2/alg_grob_L2_013`

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

- `lm'_add_le_of_both_lm'_le`
- `lm_add_le_of_both_lm_le`
- `lm_add_le_of_both_lm_le_mon`

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

1. Lemma (lm'_add_le_of_both_lm'_le)
   The lemma must be named `lm'_add_le_of_both_lm'_le`.
   Matched text (candidate 0, paragraph): Lemma (Cox, IVA, Ch.2, Sec.2, Lemma 8) Upper bound of the leading monomial of addition
2. Lemma (lm_add_le_of_both_lm_le)
   The lemma must be named `lm_add_le_of_both_lm_le`.
   Matched text (candidate 1, paragraph): Let $f_1, f_2 \in R[\sigma]$ be multivariate polynomials (which might be zero). Here,
                                          $\sigma$ is a set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a
                                          nontrivial commutative semiring. Given a monomial $x^\delta$ such that $\mathrm{LM}(f_1) \le
                                          x^\delta$ and $\mathrm{LM}(f_2) \le x^\delta$, we have $\mathrm{LM}(f_1 + f_2) \le
                                          x^\delta$.
3. Lemma (lm_add_le_of_both_lm_le_mon)
   The lemma must be named `lm_add_le_of_both_lm_le_mon`.
   Matched text (candidate 2, paragraph): Proof) It suffices to take a polynomial $g \in R[\sigma]$ whose leading monomial is
                                          $\delta$. Such polynomial exists from $R \ne \{0\}$; in particular, $g$ can be taken as the
                                          monomial $cx^\delta$ for some $c \in R \setminus \{0\}$. Now we obtain the result from the
                                          same inequality for $f_1, f_2$ and $g$.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
