# Formalization Blueprint: `algebra/L2/alg_grob_L2_024`

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
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Henselian
```

## Required Names

- `mem_monmul_supp_iff`

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
Formalize in Lean the Lemma (mem_monmul_supp_iff) from Text.

The lemma must be named `mem_monmul_supp_iff`.
   Matched text (candidate 0, lemma, label=mem_monmul_supp_iff): Lemma (mem_monmul_supp_iff) Let $K[\sigma]$ be a ring of multivariate polynomials, where
                                                                 $\sigma$ is a set of variable symbols, and $K$ is a field. For two exponent tuples $\mu, \nu
                                                                 \in \mathbb{Z}_{\ge 0}^{\oplus \sigma}$, $x^\mu$ divides $x^\nu$ if and only if there exists
                                                                 a polynomial $f \in K[\sigma]$ such that $x^\nu$ is in $x^\mu f$.
-/
```
