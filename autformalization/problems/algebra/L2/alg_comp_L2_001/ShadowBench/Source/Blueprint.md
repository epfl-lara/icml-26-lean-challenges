# Formalization Blueprint: `algebra/L2/alg_comp_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: final draft location for the source theorem. Contains two representation-bridge definitions and the theorem skeleton `minimal_monomial_mem_generators`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

No split into additional generated files is currently useful: the source has a single theorem and two small bridge definitions.

## Import Plan

```lean
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.MonomialOrder
```

These are the direct imports in `ShadowBench/Source/Main.lean`; the root project modules already import the generated target module path.

## Suggested Search Modules

- `Mathlib.RingTheory.MvPolynomial.Ideal`: `MvPolynomial.mem_ideal_span_monomial_image` bridges membership in a monomial ideal to divisibility/componentwise exponent domination by a generator.
- `Mathlib.Data.Finsupp.MonomialOrder`: `MonomialOrder`, `MonomialOrder.le_add_right`, and notation `≼[m]`, `≺[m]` for comparing exponent vectors under a monomial order.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial.monomial`, `MvPolynomial.support_monomial`, and support/coefficient lemmas.

## Required Names

- `minimal_monomial_mem_generators`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` are identical. They provide the required theorem name and import hints, but their statement is not retained verbatim: it writes `MvPolynomial.X α` for an exponent vector `α`, uses an ad hoc relation `lt`, and states strict minimality `∀ β ∈ S, lt min_elem β`, which cannot hold at `β = min_elem` for an irreflexive order.
- `docs/skeletons/Skeleton4.lean` repeats the same candidate and additionally has malformed Lean (`:= by sorry` after an already completed theorem skeleton), so it is used only as a negative syntax warning.
- The final draft adopts the required name and import block from the instructions/skeletons, but replaces the candidate relation with Mathlib's `MonomialOrder σ`, replaces `x^α` by `MvPolynomial.monomial α 1`, and formalizes “the smallest element of `S`” as a chosen exponent `μ ∈ S` satisfying `∀ β ∈ S, μ ≼[m] β`.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem lines 17-19 (`line-17`).
- Planned Lean declarations: `monomialIdealFromExponents`, `idealExponentSet`, `minimal_monomial_mem_generators`.
- Formal statement review: The Lean theorem keeps the source data `A`, `I`, and `S`, adds bridge equalities `hI : I = monomialIdealFromExponents A` and `hS : S = idealExponentSet I`, quantifies over an arbitrary `m : MonomialOrder σ`, and represents “the smallest element of S” by hypotheses `μ ∈ S` and `∀ β ∈ S, μ ≼[m] β`; the conclusion is exactly `μ ∈ A`.
- Source qualifiers: monomial ideal in a multivariate polynomial ring; generating exponents `A`; ideal equality `I = ⟨x^α | α ∈ A⟩`; exponent set `S` consisting of supports of ideal elements; arbitrary monomial order; chosen least exponent of `S`; output codomain/conclusion is the proposition that this exponent lies in `A`.
- Lean coverage: `MvPolynomial.monomial α (1 : R)` represents `x^α`; `monomialIdealFromExponents` represents the generated monomial ideal; `idealExponentSet` represents exponents occurring in monomials of `I`; Mathlib `MonomialOrder σ` represents the source monomial order; leastness under `≼[m]` represents the smallest-element hypothesis.
- Scope changes: coefficient domain is explicit as `[CommSemiring R] [Nontrivial R]`; smallest element is represented by membership plus leastness hypotheses instead of an argmin construction; the ad hoc skeleton strict relation is replaced by Mathlib's structured monomial order.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no source proof is supplied. For the later proof, use `MvPolynomial.mem_ideal_span_monomial_image` on a polynomial witnessing `μ ∈ idealExponentSet I` to obtain `α ∈ A` with `α ≤ μ`; show `α ∈ S` from the monic generator, derive `α ≼[m] μ`, combine with leastness `μ ≼[m] α`, use antisymmetry via `m.toSyn`, and conclude `μ = α` and hence `μ ∈ A`.

## Source Inventory

1. `line-17` (theorem, lines 17-19)
   - Planned Lean declaration: `minimal_monomial_mem_generators`
   - Source locator: `docs/source.tex`, lines 17-19
   - Source statement: Suppose that $I = \langle x^\alpha \mid \alpha \in A \rangle$ is a monomial ideal, and let $S$ be the set of all exponents that occur as monomials of $I$. Then, for any monomial order $>$, prove that the smallest element of $S$ with respect to $>$ must lie in $A$.

- `line-17` (theorem, lines 17-19) - `minimal_monomial_mem_generators`.
- Source inventory entry `line-17`.
- Source inventory entry: `line-17`.
- Source inventory label: `line-17`.
- Planned Lean declaration: `minimal_monomial_mem_generators`.
- Source label: `line-17`.
- Source locator: `line-17`.
- Source file: `docs/source.tex`.
- Source environment: theorem.
- Source theorem lines: 17-19.
- Source statement: Suppose that $I = \langle x^\alpha \mid \alpha \in A \rangle$ is a monomial ideal, and let $S$ be the set of all exponents that occur as monomials of $I$. Then, for any monomial order $>$, prove that the smallest element of $S$ with respect to $>$ must lie in $A$.
- Complete source proof: none supplied in `docs/source.tex`.
- Lean declaration: `minimal_monomial_mem_generators` in `ShadowBench/Source/Main.lean`.
- Lean coverage: bridge definitions record the monomial-ideal and exponent-set representations; the theorem uses `MonomialOrder σ` and a leastness hypothesis under `≼[m]`.
- Scope changes: coefficient domain made explicit as `[CommSemiring R] [Nontrivial R]`; smallest element represented by hypotheses rather than an argmin construction.
- Dependencies: `MvPolynomial.monomial`, `Ideal.span`, `MvPolynomial.support`, `MonomialOrder`; proof hints include `MvPolynomial.mem_ideal_span_monomial_image`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Statement Inventory

### `line-17` — source theorem, `docs/source.tex` lines 17–19

- Source inventory entry: `line-17`
- Source locator: `line-17` (`docs/source.tex`, lines 17–19)
- Environment: `theorem`

Source statement:

> Suppose that $I = \langle x^\alpha \mid \alpha \in A \rangle$ is a monomial ideal, and let $S$ be the set of all exponents that occur as monomials of $I$. Then, for any monomial order $>$, prove that the smallest element of $S$ with respect to $>$ must lie in $A$.

Planned Lean declarations:

- Bridge definition `ShadowBench.Source.monomialIdealFromExponents`:
  `Ideal.span ((fun α => MvPolynomial.monomial α (1 : R)) '' A)`, formalizing `⟨x^α | α ∈ A⟩`.
- Bridge definition `ShadowBench.Source.idealExponentSet`:
  `{α | ∃ f ∈ I, α ∈ f.support}`, formalizing “the set of all exponents that occur as monomials of `I`”.
- Source theorem `minimal_monomial_mem_generators`:
  for `A`, `I`, `S`, a proof `hI : I = monomialIdealFromExponents A`, a proof `hS : S = idealExponentSet I`, any `m : MonomialOrder σ`, and any `μ ∈ S` least under `m`, conclude `μ ∈ A`.

Skeleton candidate used:

- Skeletons 1–3 shaped the import block and required declaration name only.
- The theorem statement was corrected for source fidelity and Lean type correctness as described above.

Dependencies:

- Direct Lean definitions: `MvPolynomial.monomial`, `Ideal.span`, polynomial `support`, and `MonomialOrder` notation.
- Expected proof dependencies for the later `/prove` phase: `MvPolynomial.mem_ideal_span_monomial_image`, `MvPolynomial.support_monomial`, componentwise `Finsupp` order/addition facts such as `le_iff_exists_add`, and antisymmetry for `m.toSyn` after translating `≼[m]` inequalities.

Formal statement review:

- The source’s unspecified polynomial coefficient domain is made explicit as a nontrivial commutative semiring `R`. This includes the usual field coefficient case for monomial ideals and avoids the degenerate zero-ring behavior where monomial supports collapse.
- The source’s monomials `x^α` are represented by Mathlib monic monomials `MvPolynomial.monomial α (1 : R)`.
- The source phrase “smallest element of `S`” is represented by an arbitrary element `μ` with hypotheses `μ ∈ S` and `∀ β ∈ S, μ ≼[m] β`, rather than by choosing a computable minimum. This preserves the claim “the smallest element, if given, belongs to `A`” without adding an extra existence theorem.
- The source says “for any monomial order `>`”; Lean uses `m : MonomialOrder σ` and its induced non-strict order `≼[m]` for leastness. This is the standard Mathlib representation of a monomial order.

Source qualifiers:

- Mathematical object class: monomial ideals in a multivariate polynomial ring.
- Generating representation: `I = ⟨x^α | α ∈ A⟩`.
- Exponent set: `S` is exactly the set of exponent vectors appearing in supports of elements of `I`.
- Quantifier order: choose exponents `A`, ideal `I`, equality proof for the monomial ideal representation, set `S`, equality proof for the exponent-set representation, then an arbitrary monomial order and a least element of `S`.
- Parameter domain: exponent vectors are finitely supported functions `σ →₀ ℕ`; coefficients lie in a nontrivial commutative semiring `R`.
- Equality/image condition: monomial generators are the image of `A` under `α ↦ MvPolynomial.monomial α 1`; `S` equals the support-exponent set of `I`.
- Side conditions: a candidate least exponent must be in `S` and must be least for the monomial order. No nonemptiness assumption is separately needed because membership of the candidate supplies it.
- Output codomain/conclusion: a proposition, specifically membership `μ ∈ A` for the chosen least exponent.
- Follow-on claim: the least exponent belongs to `A`.

Lean coverage:

- Coverage is exact for the algebraic content after the two explicit representation bridges: monomial ideal generated by `A`, exponent set of the ideal, arbitrary Mathlib monomial order, and proposition-valued conclusion membership `μ ∈ A`.
- Coverage is parameterized over an explicit coefficient domain because the source omits one. The chosen `R`-generic statement covers the standard field case and is not a simplification to a single concrete ring.

Scope changes:

- Coefficient domain made explicit as `[CommSemiring R] [Nontrivial R]` because the source does not name a base field/ring.
- “Smallest element” is hypothesis-based rather than implemented with an argmin operator; this avoids adding a separate existence statement not present in the source.
- The skeleton's ad hoc strict relation assumptions are intentionally omitted and replaced by Mathlib's structured `MonomialOrder`.

Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

Source proof / prover notes:

- Complete source proof text: none is present in `docs/source.tex`.
- Proof sketch for the later prover: unfold `hS` and `idealExponentSet` to get a polynomial `f ∈ I` whose support contains the least exponent `μ`. Rewrite `hI`, then apply `MvPolynomial.mem_ideal_span_monomial_image` to `f ∈ I`; the support membership of `μ` yields a generator exponent `α ∈ A` with `α ≤ μ` componentwise. Since `α ∈ A`, the monomial `MvPolynomial.monomial α 1` lies in the ideal, so `α ∈ S` by the support of a nonzero monic monomial. Componentwise `α ≤ μ` gives `μ = α + γ` for some `γ`, hence `α ≼[m] μ` using monomial-order compatibility/additivity. Leastness of `μ` applied to `α ∈ S` gives `μ ≼[m] α`; antisymmetry after applying `m.toSyn` yields `μ = α`, and therefore `μ ∈ A`.

## Formalization Rules

```text
open MvPolynomial
open scoped MonomialOrder

/-
Formalize in Lean the named statement from the theorem in the text.

The Lean declaration must be named exactly:
- `minimal_monomial_mem_generators`

Matched text (candidate 0, theorem):
\begin{theorem}
Suppose that $I = \langle x^\alpha \mid \alpha \in A \rangle$ is a monomial ideal,
and let $S$ be the set of all exponents that occur as monomials of $I$.
Then, for any monomial order $>$, prove that the smallest element of $S$ with respect to $>$
must lie in $A$.
\end{theorem}
-/
```

## Proof-Handoff Checklist

- [x] Source document inspected and theorem inventory entry `line-17` recorded.
- [x] Candidate skeletons compared against the source and instructions.
- [x] Bridge definitions for source representations implemented without construction stubs.
- [x] Theorem statement drafted with source/prover notes in the Lean doc comment.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Proof phase removed the `sorry` in `minimal_monomial_mem_generators`.
