# Formalization Blueprint: `algebra/L2/alg_grob_L2_014`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the single source-backed theorem skeleton `lm_sum_le_of_all_lm_le`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level builds cover the generated target module.

## Import Plan

```lean
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
```

## Suggested Search Modules

- `Mathlib.RingTheory.MvPolynomial.MonomialOrder`: search for `MonomialOrder.degree`, `MonomialOrder.degree_sum_le`, and order notation `≼[m]`.
- `Mathlib.Data.Finsupp.MonomialOrder`: source of the `MonomialOrder` structure and the `≼[m]` notation, re-exported by the direct import above.

## Required Names

- `lm_sum_le_of_all_lm_le`

## Source Inventory

### Lemma: `lm_sum_le_of_all_lm_le`

- Planned Lean declaration: `lm_sum_le_of_all_lm_le`
- Source locator: `docs/source.tex`, displayed lemma titled “Upper bound of the leading monomial of finite sum”.
- Full source statement: Let `f_1, f_2, \cdots, f_n \in R[\sigma]` be multivariate polynomials, possibly zero. The variable symbols are `\sigma`, a monomial order `>` is fixed on monomials, and `R` is a nontrivial commutative semiring. Given a monomial `x^\delta` such that `LM(f_i) \le x^\delta` for every `i = 1, 2, \cdots, n`, then `LM(\sum_{i=1}^n f_i) \le x^\delta`.
- Complete source proof text: “Induction on `n`, with initial case `n = 1` assumed and `n = 2` already proven, directly gives the conclusion.”
- Skeleton candidate used: Skeletons 1–3 propose the expected name and a finite-family `Fin n` shape, but their `MvPolynomial.leadingMonomial` identifier is not the current Mathlib API for monomial-order leading monomials. Skeleton4 is malformed by an extra `:= by sorry`. The Lean draft adopts the finite-family shape and expected name, but uses `MonomialOrder.degree`, the Mathlib leading-monomial exponent for a monomial order.
- Dependencies: `MonomialOrder`, `MonomialOrder.degree`, `MonomialOrder.degree_sum_le`, finite sums over `Fin n`, and the scoped monomial-order relation `a ≼[m] b`.
- Formal statement review: The Lean theorem quantifies over variable symbols `σ`, a coefficient type `R` with `[CommSemiring R] [Nontrivial R]`, an explicit monomial order `m : MonomialOrder σ`, a positive finite length `n`, a family `f : Fin n → MvPolynomial σ R`, and a bound exponent `δ : σ →₀ ℕ`. The hypothesis `∀ i, m.degree (f i) ≼[m] δ` is the Lean form of `LM(f_i) ≤ x^δ`, and the conclusion `m.degree (∑ i : Fin n, f i) ≼[m] δ` is the Lean form of the leading monomial of the finite sum being bounded by `x^δ`.
- Source qualifiers:
  - Mathematical object class: multivariate polynomials over the variable-symbol type `σ` with coefficients in a nontrivial commutative semiring `R`.
  - Quantifier order: choose `σ`, `R`, algebraic instances, fixed monomial order `m`, finite length `n`, family `f`, bound exponent `δ`, then assume all individual leading monomial bounds.
  - Parameter domain: `f` is a positive finite family indexed by `Fin n`; `δ : σ →₀ ℕ` encodes the monomial `x^δ`.
  - Order condition: each leading monomial exponent is at most `δ` in the fixed monomial order.
  - Output condition: the leading monomial exponent of the finite sum is at most `δ` in the same monomial order.
  - Zero-polynomial side condition: each `f i` may be zero; Mathlib defines `m.degree 0 = 0`, so no nonzero assumption is added.
  - Follow-on claims: none beyond the bound for the finite sum.
- Lean coverage:
  - `MvPolynomial σ R` covers `R[σ]`.
  - `[CommSemiring R] [Nontrivial R]` covers the coefficient assumptions.
  - `m : MonomialOrder σ` covers the fixed monomial order.
  - `n : ℕ` and `hn : 0 < n` with `Fin n` covers the source family `i = 1, …, n`.
  - `m.degree p` covers the exponent of the leading monomial `LM(p)` in Mathlib’s monomial-order API.
  - `δ : σ →₀ ℕ` covers the exponent vector of the monomial `x^δ`.
  - `≼[m]` covers comparison in the fixed monomial order.
- Scope changes: none intended. The use of `m.degree` records the standard Mathlib representation of the leading monomial exponent rather than the polynomial term `x^δ`; the exponent/vector representation is the same data compared by a monomial order.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: The source proof argues by induction using the two-summand case. In Mathlib, the direct proof should use `MonomialOrder.degree_sum_le` for the finite sum over `Finset.univ`, then show the supremum of the individual degrees is at most `δ` using the hypothesis and `Finset.sup_le_iff`/`Finset.sup_le`. The positive-length assumption `hn` is for source fidelity and should not be needed by the direct Mathlib proof.

## Handoff Checklist

- [x] Source document and manifest inspected.
- [x] Candidate skeletons compared against the source and current Mathlib API.
- [x] Blueprint source inventory, dependencies, statement-fidelity review, and prover notes filled in.
- [x] Target Lean file drafted with imports first and a source-aware theorem doc comment.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Prover queue eliminated the theorem `sorry`.
