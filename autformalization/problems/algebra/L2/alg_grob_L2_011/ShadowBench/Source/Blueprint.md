# Formalization Blueprint: `algebra/L2/alg_grob_L2_011`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- Decision: keep a single generated Lean file. The source has one notation bridge and one source lemma, so splitting would add import overhead without improving organization.
- `ShadowBench/Source/Main.lean`: contains the source notation bridge `leadingMonomial` and the source lemma `lm'_add_le_of_both_lm'_le`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

The existing root project module imports the generated target module path, so project verification checks `ShadowBench/Source/Main.lean` through `ShadowBench.lean`.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
```

## Suggested Search Modules

- `Mathlib.RingTheory.MvPolynomial.MonomialOrder`: useful later for proof search, especially `MonomialOrder.degree`, `MonomialOrder.degree_le_iff`, and `MonomialOrder.degree_add_le`.
- `Mathlib.Algebra.MvPolynomial.Basic`: polynomial support and addition facts.
- `Mathlib.Data.Finsupp.MonomialOrder`: `MonomialOrder` and scoped order notation `≼[m]`, `≺[m]`.

## Required Names

- `lm'_add_le_of_both_lm'_le`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` all propose the required theorem name and the source nonzero hypotheses, but they use a nonexistent `MvPolynomial.leadingMonomial` and model the monomial order as `[LinearOrder (Finsupp σ ℕ)]`. That loses the source datum of a fixed monomial order.
- `docs/skeletons/Skeleton4.lean` has the same proposed statement shape and an extra malformed `:= by sorry`, so it is not adopted.
- Final draft choice: keep the required theorem name and source nonzero hypotheses, but formalize `LM(f)` through the local bridge `leadingMonomial m f`. This bridge is defined as the supremum of `f.support` transported through the fixed `m : MonomialOrder σ`, matching Mathlib's `MonomialOrder.degree` formula without adding an extra direct import during drafting.

## Statement Inventory

### Lemma `lm'_add_le_of_both_lm'_le`

- Planned Lean declaration: theorem `lm'_add_le_of_both_lm'_le` in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, lines 17--23.
- Source statement: Let `f₁`, `f₂`, and `g` be nonzero multivariate polynomials in `R[σ]`; assume `f₁ + f₂` is nonzero. A fixed monomial order on `σ` is given, and `R` is a commutative semiring. If `LM(f₁) ≤ LM(g)` and `LM(f₂) ≤ LM(g)`, then `LM(f₁ + f₂) ≤ LM(g)`.
- Source proof text: "It is assumed that no monomials in `f₁` or `f₂` are greater than `LM(g)`, under the fixed monomial order. Since the monomials in `f₁ + f₂` must be in at least one of `f₁` and `f₂`, those monomials still can't be greater than `LM(g)`, hence the inequality."
- Dependencies: local bridge `leadingMonomial`, `MvPolynomial.support`, `MonomialOrder.toSyn`, scoped notation `≼[m]`, and the assumptions `h₁`, `h₂`.
- Formal statement review: The Lean theorem quantifies over `{R σ : Type*}`, `[CommSemiring R]`, a fixed `m : MonomialOrder σ`, and polynomials `f₁ f₂ g : MvPolynomial σ R`. It includes all source nonzero assumptions: `f₁ ≠ 0`, `f₂ ≠ 0`, `g ≠ 0`, and `f₁ + f₂ ≠ 0`. The two hypotheses and conclusion use `leadingMonomial m _ ≼[m] leadingMonomial m g`, i.e. comparison under the same fixed monomial order.
- Source qualifiers:
  - Mathematical object class: multivariate polynomials `MvPolynomial σ R` over a commutative semiring.
  - Variable symbols: arbitrary type `σ`; no finiteness assumption is imposed because Mathlib multivariate polynomials have finite monomial support.
  - Fixed order: explicit parameter `m : MonomialOrder σ`.
  - Nonzero side conditions: `f₁`, `f₂`, `g`, and `f₁ + f₂` are all assumed nonzero as in the source.
  - Inequality condition: both hypotheses and the conclusion are comparisons under `m`.
- Lean coverage: full source coverage modulo the recorded notation bridge `leadingMonomial m f := m.toSyn.symm (f.support.sup m.toSyn)`, which is the leading monomial exponent of `f` under `m`.
- Scope changes: no mathematical weakening or strengthening intended. The draft represents the source's `LM` as a leading monomial exponent, not as a coefficient-bearing leading term polynomial.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Open `MonomialOrder` scoped notation. The proof shows that every support exponent of `f₁ + f₂` is in the support of `f₁` or `f₂` after using the coefficient-addition formula, then applies the two upper bounds using `Finset.le_sup` and transitivity. The source nonzero assumptions are retained in the statement for source fidelity.

## Review Gate Checklist

- [x] Source document inspected.
- [x] Companion instructions and skeletons reviewed.
- [x] Local/Mathlib search performed before drafting.
- [x] Blueprint source map and statement-fidelity notes filled in.
- [x] Lean draft contains the source theorem statement and source-aware prover notes.
- [x] Project-level Lean verification passed cleanly after proof completion.
- [x] Manual needs-review audit approved every source entry on 2026-06-05.
- [x] Target Lean file has no `sorry`, `admit`, or open goals.
