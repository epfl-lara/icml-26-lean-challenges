# ShadowBench Instructions: `algebra/L2/alg_grob_L2_024`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Henselian
```

## Expected Declaration Names

- `mem_monmul_supp_iff`
- `ABM_algebra_L2_alg_grob_L2_024_item_2`
- `ABM_algebra_L2_alg_grob_L2_024_item_3`

## Formalization Rules

```text
/-
Formalize in Lean the following named items from Text.

1. Lemma (mem_monmul_supp_iff)
   The lemma must be named `mem_monmul_supp_iff`.
   Matched text (candidate 0, paragraph): Lemma (Cox, IVA, Ch.2, Sec.4, Lemma 2; substep)
2. Theorem (ABM_algebra_L2_alg_grob_L2_024_item_2)
   The theorem must be named `ABM_algebra_L2_alg_grob_L2_024_item_2`.
   Matched text (candidate 1, paragraph): Let $K[\sigma]$ be a ring of multivariate polynomials, where $\sigma$ is a set of variable
                                          symbols, and $K$ is a field. For two exponent tuples $\mu, \nu \in \mathbb{Z}_{\ge
                                          0}^{\oplus \sigma}$, $x^\mu$ divides $x^\nu$ if and only if there exists a polynomial $f \in
                                          K[\sigma]$ such that $x^\nu$ is in $x^\mu f$.
3. Theorem (ABM_algebra_L2_alg_grob_L2_024_item_3)
   The theorem must be named `ABM_algebra_L2_alg_grob_L2_024_item_3`.
   Matched text (candidate 2, paragraph): Proof) (==>) It suffices to take $f$ as $x^{\nu - \mu}$. (<==) Take $f$ satisfying the
                                          assumption. Then there exists a monomial $x^\alpha$ in $f$ such that $x^\nu = x^{\alpha +
                                          \mu}$, and thus $x^\mu \mid x^{\alpha + \mu} = x^\nu$.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
