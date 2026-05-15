# ShadowBench Instructions: `algebra/L2/alg_grob_L2_014`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
```

## Expected Declaration Names

- `lm_add_le_of_both_lm_le`
- `lm_add_le_of_both_lm_le_mon`
- `lm_sum_le_of_all_lm_le`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
