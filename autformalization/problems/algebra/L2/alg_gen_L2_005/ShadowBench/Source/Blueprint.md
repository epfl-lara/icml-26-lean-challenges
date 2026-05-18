# Formalization Blueprint: `algebra/L2/alg_gen_L2_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: planner draft created; awaiting independent statement/source verification.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: source-backed definition `S` and theorem skeleton `zeroLocus_nonempty_of_disjoint_S`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source.Main` and `ShadowBench.Source`.

## Import Plan

```lean
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span
```

## Suggested Search Modules

- `Mathlib.RingTheory.Nullstellensatz` for `MvPolynomial.zeroLocus`, `MvPolynomial.mem_zeroLocus_iff`, `MvPolynomial.zeroLocus_span`, and vanishing-ideal lemmas.
- `Mathlib.Algebra.MvPolynomial.Eval` for evaluation lemmas when unfolding `S`.

## Required Names

- `S`

## Source Statement Inventory

### line-16

- Source locator: `docs/source.tex`, lines 16--18.
- Source kind: definition environment titled `S`, containing a theorem-like request.
- Complete source text: "Let $k$ be an arbitrary field and let $S$ be the subset of all polynomials in $k[x_1,\dots,x_n]$ that have no zeros in $k^n$. If $I$ is any ideal in $k[x_1,\dots,x_n]$ such that $I \cap S=\varnothing$, show that $\mathbf V(I)\neq\varnothing$."
- Planned Lean declarations: `S`, `zeroLocus_nonempty_of_disjoint_S`
- Dependencies: `MvPolynomial (Fin n) k`, `Fin n → k`, `MvPolynomial.eval`, `Ideal (MvPolynomial (Fin n) k)`, ideal-to-set coercion, `MvPolynomial.zeroLocus k I`.
- Formal statement review:
  - `S k n` is `{p : MvPolynomial (Fin n) k | ∀ x : Fin n → k, MvPolynomial.eval x p ≠ 0}`, matching the source subset of polynomials in `k[x_1, ..., x_n]` with no zeros in `k^n`.
  - `zeroLocus_nonempty_of_disjoint_S` quantifies `k : Type u`, `[Field k]`, `n : ℕ`, and `I : Ideal (MvPolynomial (Fin n) k)`, matching the source field, finite variable list, and arbitrary ideal.
  - The hypothesis `((I : Set (MvPolynomial (Fin n) k)) ∩ S k n) = ∅` encodes `I ∩ S = ∅`.
  - The conclusion `(MvPolynomial.zeroLocus k I).Nonempty` encodes `\mathbf V(I) ≠ ∅` as nonemptiness of the common `k`-rational zero locus.
- Source qualifiers:
  - Mathematical object class: arbitrary field `k`; finite polynomial ring `k[x_1, ..., x_n]`; ideal of that ring; subset `S` of polynomials.
  - Quantifier order: field, number of variables, ideal, disjointness hypothesis, nonempty variety conclusion.
  - Parameter domain: points are `k`-valued `n`-tuples; polynomials have coefficients in the same field `k`.
  - Output codomain: proposition asserting nonemptiness of the zero locus.
  - Equality/image condition: `I ∩ S = ∅` represented by set equality to `∅`; `\mathbf V(I)` represented by `MvPolynomial.zeroLocus k I`.
  - Side conditions: no algebraic-closure, finite-field, or nonempty-variable-list assumption is added.
- Lean coverage:
  - The source polynomial ring is represented by `MvPolynomial (Fin n) k`.
  - The source affine space `k^n` is represented by `Fin n → k`.
  - The named source definition is represented by `S`.
  - The source implication from `I ∩ S = ∅` to `\mathbf V(I) ≠ ∅` is represented by `zeroLocus_nonempty_of_disjoint_S`.
- Scope changes:
  - No weakening or omission of the source implication.
  - Representation bridge: variables are indexed by `Fin n` rather than by printed symbols `x_1, ..., x_n`; affine points are functions `Fin n → k`.
  - Variable-count convention: Lean quantifies over `n : ℕ`, including `n = 0`; this is a harmless strengthening if the source notation `x_1, ..., x_n` is read as requiring `n > 0`.
- Statement verification status: drafted; awaiting independent statement/source verification.
- Source proof / prover notes:
  - The source gives no separate proof beyond the problem statement.
  - Natural route: extend `I`, using Zorn/localization at the multiplicative set `S`, to a maximal ideal still disjoint from `S`. Zariski's lemma makes the residue field algebraic over `k`; if a residue coordinate were not in `k`, its minimal polynomial would yield an element of `S` inside the maximal ideal. The resulting `k`-valued coordinates should be a common zero of `I`.
  - Useful Mathlib names from search: `MvPolynomial.zeroLocus`, `MvPolynomial.mem_zeroLocus_iff`, `MvPolynomial.zeroLocus_span`, `MvPolynomial.vanishingIdeal`, and maximal-ideal/Zariski-lemma infrastructure around `MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing`.

## Handoff Notes

- The declaration skeleton intentionally leaves the theorem proof to the managed `/prove` queue after statement/source review.
- Do not mark the statement verification status as approved until an independent reviewer has compared the Lean declarations against `docs/source.tex`.
- Suggested next proof command after review: `/prove ShadowBench/Source/Main.lean zeroLocus_nonempty_of_disjoint_S`.
