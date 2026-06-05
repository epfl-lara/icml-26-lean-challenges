# Formalization Blueprint: `algebra/L3/alg_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single generated Lean file containing the source-backed theorem skeleton.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level `lake build` covers the generated target module.

## Import Plan

```lean
import Mathlib.RingTheory.Polynomial.UniqueFactorization
```

Direct import alignment: `ShadowBench/Source/Main.lean` uses exactly the direct Lean import listed above.

## Suggested Search Modules

These are proof-search hints only, not current direct imports:

- `Mathlib.RingTheory.Ideal.Operations` for `Ideal.radical` membership and radical lemmas.
- `Mathlib.RingTheory.Ideal.Span` for principal ideals as singleton spans.
- `Mathlib.RingTheory.Radical.Basic` for UFD radical lemmas such as `UniqueFactorizationMonoid.radical_prod`.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`.
- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` are identical candidate statements using a `List` of factors and a zipped `List` of exponents.
- `docs/skeletons/Skeleton4.lean` repeats that candidate and contains an extra malformed trailing `:= by sorry`.
- Skeleton influence: the final theorem preserves the required declaration name and the use of `MvPolynomial`, `Ideal.radical`, and a singleton `Ideal.span`; it replaces the zipped-list representation with a `Fin r` indexed family so the source parameters `f_1, …, f_r` and `a_1, …, a_r` have matching lengths by construction. It also uses `MvPolynomial.C c * ...` instead of scalar multiplication to spell out multiplication by the coefficient polynomial.

## Required Names

- `radical_span_singleton_eq_span_prod_irreducibles`

## Source Statement Inventory

- `prop:radical-principal`: theorem from `docs/source.tex` lines 17-28, formalized as `radical_span_singleton_eq_span_prod_irreducibles`.

### prop:radical-principal

- Source inventory entry `prop:radical-principal`
- Source inventory entry: `prop:radical-principal`.
- Source inventory entry: prop:radical-principal
- Source label: `prop:radical-principal`.
- Source label: prop:radical-principal
- Label: `prop:radical-principal`.
- Label: prop:radical-principal
- Source inventory ID: `prop:radical-principal`.
- Source inventory ID: prop:radical-principal
- Source kind: theorem.
- Source title/name: `radical_span_singleton_eq_span_prod_irreducibles`.
- Source locator: `docs/source.tex`, theorem lines 17-28; proof environment lines 30-48, with proof body lines 31-47.
- Planned Lean declarations: `radical_span_singleton_eq_span_prod_irreducibles` in `ShadowBench/Source/Main.lean`.
- Lean statement:

```lean
theorem radical_span_singleton_eq_span_prod_irreducibles
    (k : Type*) [Field k] (n r : ℕ)
    (f : MvPolynomial (Fin n) k) (c : k)
    (factors : Fin r → MvPolynomial (Fin n) k) (exponents : Fin r → ℕ)
    (h_c_ne_zero : c ≠ 0)
    (h_exponents_pos : ∀ i, 0 < exponents i)
    (h_irreducible : ∀ i, Irreducible (factors i))
    (h_distinct : Pairwise (fun i j => ¬ Associated (factors i) (factors j)))
    (h_factorization :
      f = MvPolynomial.C c * ∏ i : Fin r, factors i ^ exponents i) :
    Ideal.radical (Ideal.span ({f} : Set (MvPolynomial (Fin n) k))) =
      Ideal.span ({∏ i : Fin r, factors i} : Set (MvPolynomial (Fin n) k))
```

- Dependencies: `MvPolynomial (Fin n) k`; `Field k`; `Ideal.span`; `Ideal.radical`; finite products over `Fin r`; `Irreducible`; `Associated`; `Pairwise`; natural-number exponents.
- Source qualifiers:
  - Mathematical object class: multivariate polynomial ring `k[x_1, …, x_n]` over a field `k`.
  - Quantifier order and parameters: field `k`, number of variables `n`, polynomial `f`, scalar `c`, finitely many factors `f_i`, and positive exponents `a_i`.
  - Parameter domain bridge: `k[x_1, …, x_n]` is represented by the standard Lean type `MvPolynomial (Fin n) k`; the finite families `f_1, …, f_r` and `a_1, …, a_r` are represented by functions out of `Fin r`, so matching lengths are built into the domain.
  - Principal ideal: `I = ⟨f⟩`.
  - Factorization side condition: `f = c f_1^{a_1} … f_r^{a_r}`.
  - Scalar side condition: source says `c ∈ k`; as a factorization coefficient in a field, the formal statement records the implicit nonzero coefficient assumption `c ≠ 0`.
  - Exponent side condition: each exponent is positive (`a_i ≥ 1`), formalized as `0 < exponents i`.
  - Irreducible factor side condition: every `f_i` is irreducible.
  - Distinctness side condition: the source says the irreducibles are distinct; formalized as pairwise non-associated, the UFD-relevant form of distinct irreducible factors after units are absorbed into `c`.
  - Output codomain: equality of ideals of `MvPolynomial (Fin n) k`.
  - Equality/image condition: `sqrt(⟨f⟩) = ⟨f_1 f_2 … f_r⟩`; the intermediate source equality `sqrt(I) = sqrt(⟨f⟩)` is covered by using `I` definitionally as `Ideal.span {f}`.
  - Follow-on claims in the theorem statement: no separate corollary follows the displayed equality; the displayed `sqrt(I) = sqrt(⟨f⟩) = ...` chain is fully represented by the single Lean equality after expanding `I`.
- Lean coverage: resolved; full coverage of the principal-radical equality in the multivariate polynomial ring `MvPolynomial (Fin n) k`. The Lean theorem covers the polynomial-ring domain, the principal ideal, the factorization equation, positive exponents, irreducibility, distinctness up to association, output equality of ideals, and the displayed `sqrt(I) = sqrt(⟨f⟩) = ...` chain after expanding `I`. The standard Lean representation uses `MvPolynomial (Fin n) k`, `Fin r`-indexed families, `MvPolynomial.C c` for the coefficient polynomial, and `Ideal.span {f}` for the defined ideal `I`; all source statement content is represented.
- Scope changes:
  - The family of factors is represented by `Fin r → MvPolynomial (Fin n) k` and exponents by `Fin r → ℕ`, instead of informal indexed symbols or a list. This is a representation bridge, not a mathematical weakening.
  - The coefficient assumption `c ≠ 0` is made explicit because the theorem is false for a zero coefficient.
  - Distinctness is stated as pairwise non-association rather than syntactic inequality; this matches the uniqueness-of-factorization proof step where irreducibles are considered up to units.
  - No separate Lean variable `I` is introduced, since the source defines `I` to be `⟨f⟩` and the theorem directly uses `Ideal.span {f}`.
- Formal statement review: the Lean statement preserves the source theorem's domain, principal ideal, factorization hypotheses, positivity of exponents, irreducibility and distinctness of factors, and final radical/principal-ideal equality. The explicit `c ≠ 0` and pairwise non-association clarify assumptions implicit in the source proof.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
First we show that $f_1 f_2\cdots f_r \in \sqrt{I}$.
Choose an integer $N$ strictly larger than $\max\{a_1,\dots,a_r\}$.
Then
\[
c (f_1 f_2\cdots f_r)^N
=
f_1^{N-a_1} f_2^{N-a_2}\cdots f_r^{N-a_r}\, f,
\]
so $(f_1 f_2\cdots f_r)^N \in I$, hence $f_1 f_2\cdots f_r \in \sqrt{I}$.
Therefore $\langle f_1 f_2\cdots f_r\rangle \subseteq \sqrt{I}$.

For the reverse inclusion, let $g\in \sqrt{I}$.
Then $g^M\in I=\langle f\rangle$ for some positive integer $M$,
so $g^M$ is divisible by $f$ and hence by each irreducible factor $f_i$.
Using unique factorization (and that irreducibles behave as primes here),
each $f_i$ must divide $g$, so $f_1 f_2\cdots f_r$ divides $g$.
Thus $g\in \langle f_1 f_2\cdots f_r\rangle$, i.e. $\sqrt{I}\subseteq \langle f_1 f_2\cdots f_r\rangle$.
```

- Source proof / prover notes: prove both ideal inclusions. For `∏ f_i ∈ radical (span {f})`, choose `N` larger than all exponents and use the displayed product identity to show a power of the squarefree product lies in `(f)`. For the reverse inclusion, from `g^M ∈ (f)` get divisibility by each irreducible factor; since irreducibles are prime in the UFD `MvPolynomial (Fin n) k`, each `f_i ∣ g`; pairwise non-association then lets the product divide `g`, giving membership in the principal ideal generated by the squarefree product.

## Formalization Rules from `docs/instructions.md`

```text
open scoped BigOperators

Formalize in Lean the Theorem (radical_span_singleton_eq_span_prod_irreducibles) from Text.
The theorem must be named `radical_span_singleton_eq_span_prod_irreducibles`.
```

## Review Checklist

- [x] Source document inspected: `docs/source.tex`.
- [x] Companion instructions and candidate skeletons read.
- [x] Local/Mathlib declaration search performed before drafting.
- [x] Blueprint source inventory includes `prop:radical-principal`.
- [x] Lean theorem skeleton drafted with source proof/prover notes in the doc comment.
- [ ] Run independent statement/source verification review and apply corrections.
- [ ] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.
