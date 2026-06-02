# ShadowBench Instructions: `algebra/L2/alg_grob_L2_013`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
```

## Expected Declaration Names

- `lm_add_le_of_both_lm_le_mon`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
