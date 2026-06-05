# Formalization Blueprint: `algebra/L2/alg_gen_L2_017`

- Source document: `docs/source.tex`
- Companion instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Document Inspection

- `formalization_document_inspect docs/source.tex` succeeded; extraction status `ok`.
- Detected theorem-like block: label `lem:mem_monomialIdeal_iff_divisible`, lemma title `mem_monomialIdeal_iff_divisible`, statement lines 17-20, proof lines 20-28.
- No sections, references, citations, bibliography files, PDFs, figures, or support assets were detected by preflight.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: generated formalization for `MvPolynomial.monomialIdeal` and `MonomialOrder.mem_monomialIdeal_iff_divisible`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so plain project builds cover the generated target module.

No file split is planned for this one-lemma source document.

## Import Plan

```lean
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
```

## Suggested Search Modules

These are proof/search hints only, not direct imports for `ShadowBench/Source/Main.lean`.

- `Mathlib.RingTheory.MvPolynomial.Ideal`: source of `MvPolynomial.mem_ideal_span_monomial_image` and `MvPolynomial.mem_ideal_span_monomial_image_iff_dvd`.
- `Mathlib.Algebra.MvPolynomial.Basic`: source of monomial support and coefficient lemmas such as `MvPolynomial.support_monomial` and `MvPolynomial.coeff_monomial`.
- `Mathlib.Algebra.MvPolynomial.Division`: source of `MvPolynomial.monomial_dvd_monomial`.

## Required Names

- `MvPolynomial.monomialIdeal`
- `MonomialOrder.mem_monomialIdeal_iff_divisible`

## Candidate Skeleton Review

- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` supply the required names and the intended membership/divisibility shape, but leave the definition as a construction gap and use `(MvPolynomial.X ^ β)` for exponent-vector monomials. The final draft keeps the names and imports while replacing that notation with mathlib's `MvPolynomial.monomial β 1`.
- `Skeleton4.lean` is rejected because it contains an extra malformed `:= by sorry` after the theorem body.

## Source inventory

- label: lem:mem_monomialIdeal_iff_divisible
  source_id: lem:mem_monomialIdeal_iff_divisible
  kind: lemma
  source_title: mem_monomialIdeal_iff_divisible
  planned_lean_declaration: MonomialOrder.mem_monomialIdeal_iff_divisible
  source_locator: docs/source.tex lines 17-20, proof lines 20-28
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.

## Construction Declarations

### Definition `MvPolynomial.monomialIdeal`

- Source locator: the phrase `I = \langle x^\alpha \mid \alpha \in A \rangle` in `docs/source.tex` lines 17-18, also listed in `docs/instructions.md` lines 40-44.
- Planned Lean declaration: `MvPolynomial.monomialIdeal`
- Planned Lean statement:
  ```lean
  noncomputable def MvPolynomial.monomialIdeal {σ k : Type*} [CommSemiring k]
      (A : Set (σ →₀ ℕ)) : Ideal (MvPolynomial σ k) :=
    Ideal.span ((fun α : σ →₀ ℕ => MvPolynomial.monomial α (1 : k)) '' A)
  ```
- Dependencies: `Ideal.span`; `Set.image`; `MvPolynomial.monomial`.
- Formal statement review: this definition directly formalizes the source-generated ideal by taking the ideal span of the set of monic monomials indexed by `A`.
- Source qualifiers: object class is a monomial ideal in a polynomial ring; generators are exactly monic monomials `x^α` with `α ∈ A`; `A` is a set of exponent vectors.
- Lean coverage: covers the generator-set definition after representing `x^α` as `MvPolynomial.monomial α 1` and exponent vectors as `σ →₀ ℕ`.
- Scope changes: the definition is generic over a commutative semiring `k`; the lemma below specializes to a field, matching the source's coefficient field. Variable indices are generalized from the finite list `x_1, ..., x_n` to an arbitrary type `σ`; taking `σ = Fin n` recovers the source setting.
- Construction status: implemented by the displayed body; there is no definition or instance construction gap.
- Source proof / prover notes: no proof obligation is attached to this definition. During theorem proving, unfold this definition to expose `Ideal.span ((fun α => MvPolynomial.monomial α 1) '' A)`.

## Source Statement Inventory

### lem:mem_monomialIdeal_iff_divisible

- Source inventory entry `lem:mem_monomialIdeal_iff_divisible`: lemma `[mem_monomialIdeal_iff_divisible]` in `docs/source.tex`.
- Source label: `lem:mem_monomialIdeal_iff_divisible`
- Source inventory entry: `lem:mem_monomialIdeal_iff_divisible`
- Source inventory label: `lem:mem_monomialIdeal_iff_divisible`
- Source block label: `lem:mem_monomialIdeal_iff_divisible`
- Preflight label: `lem:mem_monomialIdeal_iff_divisible`
- Planned Lean declarations: `MonomialOrder.mem_monomialIdeal_iff_divisible`
- Source locator: `docs/source.tex`, lemma lines 17-20; proof lines 20-28.
- Source statement text:
  ```text
  Let I = \langle x^\alpha \mid \alpha \in A \rangle be a monomial ideal.
  Then a monomial x^\beta lies in I if and only if x^\beta is divisible by x^\alpha for some \alpha \in A.
  ```
- Complete source proof text:
  ```text
  If x^\beta is a multiple of x^\alpha for some \alpha \in A, then x^\beta \in I by the definition of ideal.
  Conversely, if x^\beta \in I, then x^\beta = \sum_{i=1}^s h_i x^{\alpha(i)}, where h_i \in k[x_1, \dots, x_n] and \alpha(i) \in A.
  If we expand each h_i as a sum of terms, we obtain
  x^\beta = \sum_{i=1}^s h_i x^{\alpha(i)} = \sum_{i=1}^s (\sum_j c_{i,j} x^{\beta(i,j)}) x^{\alpha(i)} = \sum_{i,j} c_{i,j} x^{\beta(i,j)} x^{\alpha(i)}.
  ```
- Adopted Lean statement shape:
  ```lean
  theorem MonomialOrder.mem_monomialIdeal_iff_divisible {σ k : Type*} [Field k]
      (A : Set (σ →₀ ℕ)) (β : σ →₀ ℕ) :
      MvPolynomial.monomial β (1 : k) ∈ MvPolynomial.monomialIdeal A ↔
        ∃ α ∈ A,
          MvPolynomial.monomial α (1 : k) ∣ MvPolynomial.monomial β (1 : k)
  ```
- Dependencies: `MvPolynomial.monomialIdeal`; likely proof lemmas `MvPolynomial.mem_ideal_span_monomial_image_iff_dvd`, `MvPolynomial.support_monomial`, and `MvPolynomial.monomial_dvd_monomial`.
- Formal statement review: the source monomial `x^β` is represented by the monic monomial `MvPolynomial.monomial β (1 : k)`. Membership is in the ideal generated by all source monomials indexed by `A`. Divisibility is Lean's polynomial divisibility relation between the corresponding monic monomials. The existential quantifier `∃ α ∈ A` matches "for some `α ∈ A`".
- Statement-fidelity review: the Lean theorem has the same iff direction and same generator-divisibility condition as the source. The ideal `I` is not a separate parameter because the source fixes it to be exactly the generated monomial ideal; this is represented by `MvPolynomial.monomialIdeal A`.
- Source qualifiers:
  - Mathematical object class: polynomial ring over a field `k`.
  - Variable domain: source variables `x_1, ..., x_n`; Lean exponent vectors use `σ →₀ ℕ`.
  - Generator data: `A` is a set of exponent vectors, and generators are exactly `x^α` for `α ∈ A`.
  - Input monomial: `x^β`.
  - Condition: membership in `I = ⟨x^α | α ∈ A⟩`.
  - Output condition: iff with existence of `α ∈ A` such that `x^α` divides `x^β`.
- Lean coverage:
  - `[Field k]` covers the coefficient field assumption in the source.
  - `A : Set (σ →₀ ℕ)` and `β : σ →₀ ℕ` cover exponent-vector parameters.
  - `MvPolynomial.monomialIdeal A` covers the generated monomial ideal `I`.
  - `MvPolynomial.monomial γ (1 : k)` covers each source monomial `x^γ`.
  - `∃ α ∈ A, MvPolynomial.monomial α (1 : k) ∣ MvPolynomial.monomial β (1 : k)` covers divisibility by a generator monomial.
- Scope changes: variables are generalized from finite `n` to arbitrary `σ`. This is a strengthening rather than a weakening; instantiating `σ = Fin n` recovers the finite-variable source case. The theorem is placed in namespace `MonomialOrder` solely to satisfy the expected declaration name; it does not depend on a monomial order.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: for the forward direction, unfold `MvPolynomial.monomialIdeal` and use the existing membership characterization for ideal spans of monomials. Specialize `MvPolynomial.mem_ideal_span_monomial_image_iff_dvd` to `x = MvPolynomial.monomial β 1`; since `1 ≠ 0` in a field, the support is the singleton `{β}`, leaving exactly an existential generator `α ∈ A` whose monomial divides `MvPolynomial.monomial β 1`. The reverse direction is the defining span argument: a generator divisor gives a multiple of a generator, hence an element of the ideal.

## Handoff Checklist

- [x] Source document `docs/source.tex` inspected with `formalization_document_inspect`.
- [x] Companion instructions and all four skeletons read and compared against the source.
- [x] Local/Mathlib search performed before drafting; relevant mathlib monomial-ideal lemmas recorded above.
- [x] Root module path imports the generated target module: `ShadowBench.lean` imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
