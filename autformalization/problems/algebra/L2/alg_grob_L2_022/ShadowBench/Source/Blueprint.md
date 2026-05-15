# Formalization Blueprint: `algebra/L2/alg_grob_L2_022`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
```

## Required Names

- `monomial_set`
- `monomial_set_union_distrib`
- `ABM_algebra_L2_alg_grob_L2_022_item_3`

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

1. Definition (monomial_set)
   The definition must be named `monomial_set`.
   Matched text (candidate 0, paragraph): Lemma (Cox, IVA, Ch.10, Sec.3) Commutativity of union and monomial set
2. Lemma (monomial_set_union_distrib)
   The lemma must be named `monomial_set_union_distrib`.
   Matched text (candidate 1, paragraph): Let $F, G \subseteq R[\sigma]$ be some finite subsets of multivariate polynomials, where
                                          $\sigma$ is a set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a
                                          commutative semiring. Let $\mathrm{Mon}(F)$ be the entire set of monomials in some $f \in
                                          F$. Then $\mathrm{Mon}(F) \cup \mathrm{Mon}(G) = \mathrm{Mon}(F \cup G)$.
3. Theorem (ABM_algebra_L2_alg_grob_L2_022_item_3)
   The theorem must be named `ABM_algebra_L2_alg_grob_L2_022_item_3`.
   Matched text (candidate 2, paragraph): Proof) Denote by $\mathrm{Mon}(f)$ for $f \in R[\sigma]$ the set of monomials in $f$. Then
                                          $\mathrm{Mon}(F) = \bigcup_{f \in F} \mathrm{Mon}(f)$. Using this, we obtain $$
                                          \begin{aligned} \mathrm{Mon}(F \cup G) &= \bigcup_{f \in F \cup G} \mathrm{Mon}(f) \\ &=
                                          \bigcup_{f \in F} \mathrm{Mon}(f) \cup \bigcup_{f \in G} \mathrm{Mon}(f) \\ &=
                                          \mathrm{Mon}(F) \cup \mathrm{Mon}(G). \end{aligned} $$

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
