# Formalization Blueprint: `algebra/L2/alg_grob_L2_022`

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
```

## Required Names

- `monomial_set_union_distrib`

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
Formalize in Lean the Lemma (monomial_set_union_distrib) from Text.

The lemma must be named `monomial_set_union_distrib`.
   Matched text (candidate 0, lemma, label=monomial_set_union_distrib): Lemma (monomial_set_union_distrib) Commutativity of union and monomial set Let $F, G
                                                                        \subseteq R[\sigma]$ be some finite subsets of multivariate polynomials, where $\sigma$ is a
                                                                        set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a commutative
                                                                        semiring. Let $\mathrm{Mon}(F)$ be the entire set of monomials in some $f \in F$. Then
                                                                        $\mathrm{Mon}(F) \cup \mathrm{Mon}(G) = \mathrm{Mon}(F \cup G)$.
-/
```
