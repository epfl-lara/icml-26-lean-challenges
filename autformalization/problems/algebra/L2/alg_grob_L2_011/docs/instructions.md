# ShadowBench Instructions: `algebra/L2/alg_grob_L2_011`

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

- `max_monomial'`
- `leading_monomial'`
- `lm'_add_le_of_both_lm'_le`

## Formalization Rules

```text
/-
Formalize in Lean the following named items from Text.

1. Definition (max_monomial')
   The definition must be named `max_monomial'`.
   Matched text (candidate 0, paragraph): Lemma (Cox, IVA, Ch.2, Sec.2, Lemma 8) Leading monomial of addition (nonzero case)
2. Definition (leading_monomial')
   The definition must be named `leading_monomial'`.
   Matched text (candidate 1, paragraph): Let $f_1, f_2, g \in R[\sigma]$ be nonzero multivariate polynomials, and suppose that the
                                          sum $f_1 + f_2$ is also nonzero. Here, $\sigma$ is a set of variable symbols over which a
                                          monomial order $>$ is fixed, and $R$ is a commutative semiring. Given $\mathrm{LM}(f_1) \le
                                          \mathrm{LM}(g)$ and $\mathrm{LM}(f_2) \le \mathrm{LM}(g)$, we have $\mathrm{LM}(f_1 + f_2)
                                          \le \mathrm{LM}(g)$.
3. Lemma (lm'_add_le_of_both_lm'_le)
   The lemma must be named `lm'_add_le_of_both_lm'_le`.
   Matched text (candidate 2, paragraph): Proof) It is assumed that no monomials in $f_1$ or $f_2$ are greater than $\mathrm{LM}(g)$,
                                          under the fixed monomial order. Since the monomials in $f_1 + f_2$ must be in at least one
                                          of $f_1$ and $f_2$, those monomials still can't be greater than $\mathrm{LM}(g)$, hence the
                                          inequality.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
