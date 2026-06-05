# Formalization Blueprint: `algebra/L2/alg_grob_L2_024`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file draft containing the source-backed declaration `mem_monmul_supp_iff`.
- `ShadowBench/Source.lean`: root submodule aggregator importing `ShadowBench.Source.Main`.
- `ShadowBench.lean`: project root importing `ShadowBench.Source`.

No split into additional generated Lean files is planned for this one-lemma source.

## Import Plan

Direct imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Henselian
```

These are the imports required by `docs/instructions.md`; the theorem statement only uses field structure, `MvPolynomial`, monomials, support, and polynomial divisibility.

## Suggested Search Modules

Non-gating proof-search hints for the later `/prove` phase:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial.support`, `MvPolynomial.mem_support_iff`, `MvPolynomial.support_monomial`, `MvPolynomial.monomial_mul`, `MvPolynomial.coeff_monomial_mul`, `MvPolynomial.coeff_monomial_mul'`.
- `Mathlib.Algebra.MvPolynomial.Division`: `MvPolynomial.monomial_dvd_monomial` relates divisibility of monomials to pointwise exponent order.
- `Mathlib.Algebra.MvPolynomial.NoZeroDivisors`: divisibility facts for monomials in polynomial rings if needed.
- Finsupp order/subtraction lemmas for converting `μ ≤ ν` into `ν = μ + (ν - μ)` and extracting `α` from a support monomial.

## Required Names

- `mem_monmul_supp_iff`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` proposed the expected name and high-level quantifier shape, but used `MvPolynomial.X μ` and `MvPolynomial.X ν`, where `X` expects a single variable `σ`, not an exponent tuple `σ →₀ ℕ`. The final draft keeps the name and quantifier order but replaces `X μ`/`X ν` with `MvPolynomial.monomial μ (1 : K)`/`MvPolynomial.monomial ν (1 : K)`.
- `docs/skeletons/Skeleton4.lean` has the same `X` issue and an extra malformed `:= by sorry`; it is not adopted.

## Statement Inventory

### Source lemma `mem_monmul_supp_iff`

- Planned Lean declaration: `mem_monmul_supp_iff`
- Source locator: `docs/source.tex`, unlabeled displayed item headed `Lemma (mem_monmul_supp_iff)` after `\maketitle`.
- Source statement: Let `K[σ]` be a ring of multivariate polynomials, where `σ` is a set of variable symbols and `K` is a field. For two exponent tuples `μ, ν ∈ ℤ_{≥ 0}^{⊕ σ}`, `x^μ` divides `x^ν` if and only if there exists a polynomial `f ∈ K[σ]` such that `x^ν` is in `x^μ f`.
- Planned Lean statement:
  ```lean
  theorem mem_monmul_supp_iff {K σ : Type*} [Field K]
      (μ ν : σ →₀ ℕ) :
      (MvPolynomial.monomial μ (1 : K) ∣ MvPolynomial.monomial ν (1 : K)) ↔
        ∃ f : MvPolynomial σ K,
          ν ∈ (MvPolynomial.monomial μ (1 : K) * f).support := by sorry
  ```
- Dependencies:
  - Direct statement dependencies: `Field K`, `σ →₀ ℕ`, `MvPolynomial σ K`, `MvPolynomial.monomial`, polynomial divisibility, and `MvPolynomial.support`.
  - Later proof dependencies likely include `MvPolynomial.monomial_dvd_monomial`, `MvPolynomial.monomial_mul`, `MvPolynomial.mem_support_iff`, `MvPolynomial.coeff_monomial_mul`, and Finsupp order/subtraction facts.
- Source qualifiers:
  - Mathematical object class: multivariate polynomial ring `K[σ]` over a field `K` with variable-symbol type `σ`.
  - Quantifier order: choose a field/type of coefficients `K`, variables `σ`, a field instance, then two exponent tuples `μ` and `ν`.
  - Parameter domain: `μ, ν ∈ ℤ_{≥0}^{⊕σ}`, i.e. finitely supported nonnegative exponent functions.
  - Equality/image condition: left side is monomial divisibility `x^μ ∣ x^ν`; right side asks for a polynomial multiplier whose product `x^μ f` contains the monomial exponent `ν` in its support.
  - Side conditions: `K` is a field; `σ` is represented as an arbitrary type of variables.
  - Follow-on claims: no additional claims beyond the iff.
- Lean coverage:
  - `MvPolynomial σ K` covers `K[σ]`.
  - `σ →₀ ℕ` covers `ℤ_{≥0}^{⊕σ}` as finitely supported nonnegative exponent tuples.
  - `MvPolynomial.monomial μ (1 : K)` and `MvPolynomial.monomial ν (1 : K)` cover the monomials `x^μ` and `x^ν`.
  - Polynomial divisibility `∣` covers `x^μ` divides `x^ν`.
  - `ν ∈ (MvPolynomial.monomial μ (1 : K) * f).support` covers the statement that the monomial `x^ν` is present in the product `x^μ f`.
- Scope changes: none intended. The Lean statement uses Mathlib's standard `MvPolynomial`/`Finsupp` representation rather than adding a separate notation bridge for `x^μ`; this is a direct representation of the source objects, not a weakening.
- Formal statement review: the skeleton's `MvPolynomial.X μ` expression was corrected because exponent tuples are encoded by `MvPolynomial.monomial`. The resulting Lean iff preserves the field assumption, both exponent tuple quantifiers, monomial divisibility on the left, and existence of a polynomial with `ν` in the product support on the right.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  ```text
  (==>) It suffices to take f as x^{ν - μ}.
  (<==) Take f satisfying the assumption. Then there exists a monomial x^α in f such that x^ν = x^{α + μ}, and thus x^μ | x^{α + μ} = x^ν.
  ```
- Source proof / prover notes:
  - Forward direction: from divisibility of monomials over a field, obtain `μ ≤ ν` using a monomial divisibility theorem; take `f = MvPolynomial.monomial (ν - μ) (1 : K)`. Use monomial multiplication and `ν = μ + (ν - μ)` to show `ν` is in the support of the product.
  - Reverse direction: from `ν ∈ support (monomial μ 1 * f)`, use a coefficient/support or support-of-product lemma to find an exponent `α ∈ f.support` with `ν = μ + α` (up to commutativity of addition). Then conclude `μ ≤ ν`, and hence `monomial μ 1 ∣ monomial ν 1` by the monomial divisibility theorem.

## Handoff Notes

- Draft proofs intentionally remain `by sorry` in the formalization phase.
- Do not start the prover queue until an independent statement/source review approves or corrects the Lean statement and records approval above.
- Suggested next command after review approval: `/prove ShadowBench/Source/Main.lean mem_monmul_supp_iff`.
