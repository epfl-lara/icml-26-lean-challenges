# Formalization Blueprint: `algebra/L2/alg_grob_L2_024`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Henselian
```

## Required Names

- `mem_monmul_supp_iff`
- `ABM_algebra_L2_alg_grob_L2_024_item_2`
- `ABM_algebra_L2_alg_grob_L2_024_item_3`

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
