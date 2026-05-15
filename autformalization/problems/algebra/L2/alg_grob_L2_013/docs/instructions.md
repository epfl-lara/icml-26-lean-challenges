# ShadowBench Instructions: `algebra/L2/alg_grob_L2_013`

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

- `lm'_add_le_of_both_lm'_le`
- `lm_add_le_of_both_lm_le`
- `lm_add_le_of_both_lm_le_mon`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
