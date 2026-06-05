# Formalization Blueprint: `algebra/L2/alg_grob_L2_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed leading-monomial definitions and the Lean declaration `coeff_zero_of_lt_lm`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level builds cover the generated target module.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
```

## Suggested Search Modules

- `Mathlib.RingTheory.MvPolynomial.MonomialOrder` for `MonomialOrder.degree`, `MonomialOrder.coeff_eq_zero_of_lt`, `MonomialOrder.degree_mem_support`, and related leading-coefficient facts.
- `Mathlib.Algebra.MvPolynomial.Basic` for `MvPolynomial.coeff`, `MvPolynomial.mem_support_iff`, and zero-polynomial coefficient simp lemmas.

## Required Names

- `coeff_zero_of_lt_lm`

## Source Inventory and Statement Map

### Lemma `coeff_zero_of_lt_lm`

- Lean declarations:
  - `leadingMonomialWithBot`: represents `LM(f)` as `⊥` when `f = 0`, otherwise as the exponent vector `m.degree f`.
  - `leadingMonomialWithBotLT`: compares two `WithBot (σ →₀ ℕ)` monomials using the fixed `MonomialOrder σ`; this is the explicit Lean bridge for the source's monomial-order comparison on `WithBot` monomials.
  - `leadingMonomialWithBotGT`: reverse comparison used to state `LM(g) > LM(f)`.
  - `coeff_zero_of_lt_lm`: source lemma formalizing the coefficient-vanishing statement. The Lean proof compiles, and manual source-fidelity review passed on 2026-06-05.
- Source locator: `docs/source.tex`, displayed lemma block beginning `Lemma (coeff_zero_of_lt_lm)` through the following `Proof)` paragraph.
- Skeleton candidate used: Skeletons 1--3 supplied the required theorem name and broad parameters but were not copied: they use non-existent/incorrect shapes `MvPolynomial.MonomialOrder σ` and `g.leadingMonomial`, and they omit the source's `LM(0) = ⊥` technical detail. Skeleton4 is malformed by an extra `:= by sorry`. The final draft keeps the source name and coefficient conclusion while replacing the skeleton's leading-monomial notation with Mathlib's `MonomialOrder.degree` plus an explicit `WithBot` bridge.
- Dependencies:
  - Mathlib object class: `MvPolynomial σ R`, `[CommSemiring R]`, and `m : MonomialOrder σ`.
  - Leading monomial support: `m.degree f : σ →₀ ℕ`, from `Mathlib.RingTheory.MvPolynomial.MonomialOrder`.
  - Proof fact: `MonomialOrder.coeff_eq_zero_of_lt` states that coefficients above `m.degree f` vanish.
- Formal statement review:
  - Source: for all multivariate polynomials `f, g ∈ R[σ]` over a commutative semiring and a fixed monomial order, if `g ≠ 0` and `LM(g) > LM(f)`, then the coefficient of `LM(g)` in `f` is zero; when `f = 0`, `LM(f)` is `⊥ : WithBot (σ →₀ ℕ)`.
  - Lean: for `{σ : Type*} {R : Type*} [CommSemiring R]`, `m : MonomialOrder σ`, and `f g : MvPolynomial σ R`, assume `h_g_ne_zero : g ≠ 0` and `h_order : leadingMonomialWithBotGT m (leadingMonomialWithBot m g) (leadingMonomialWithBot m f)`; conclude `f.coeff (m.degree g) = 0`.
  - The coefficient target is `m.degree g` because `h_g_ne_zero` makes `leadingMonomialWithBot m g = some (m.degree g)`.
- Source qualifiers:
  - Mathematical object class: multivariate polynomials `MvPolynomial σ R`.
  - Variable/index domain: arbitrary `σ : Type*`; no `Fintype σ` is imposed because Mathlib monomial orders and `MvPolynomial` support arbitrary variable types.
  - Coefficient domain: `R : Type*` with `[CommSemiring R]`.
  - Fixed order: explicit parameter `m : MonomialOrder σ`.
  - Side condition: `g ≠ 0`.
  - Zero-polynomial convention: `leadingMonomialWithBot m 0 = ⊥` by definition.
  - Order premise: `LM(g) > LM(f)`, represented by `leadingMonomialWithBotGT m` induced by `m` on `WithBot (σ →₀ ℕ)`.
  - Conclusion: equality `f.coeff (m.degree g) = 0`, i.e. the coefficient of `LM(g)` in `f` is zero.
- Lean coverage: exact mathematical coverage modulo the explicit representation bridge for the monomial-order comparison on `WithBot (σ →₀ ℕ)`. The theorem keeps the nonzero assumption on `g`, the commutative semiring assumption on `R`, the fixed monomial order, and the `LM(0) = ⊥` convention.
- Scope changes: no mathematical weakening or strengthening intended. Representation change only: Lean cannot install an `m`-dependent order instance on the raw type `WithBot (σ →₀ ℕ)`, so comparison is expressed by the predicate `leadingMonomialWithBotGT m` rather than by a bare `>` notation.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Since any coefficient of `f` given `f = 0` is zero, we might suppose `f ≠ 0`, so that `f` also attains a leading monomial. Thanks to the assumption `LM(g) > LM(f)`, any monomial `x^α` with nonzero coefficient in `f` satisfies `LM(g) > LM(f) ≥ x^α`. Therefore, none of such `x^α`'s equals `LM(g)`, meaning that the coefficient of `LM(g)` in `f` must be zero.
- Proof notes: split on `f = 0`. If `f = 0`, simplify coefficients. If `f ≠ 0`, unfold `leadingMonomialWithBotGT`, `leadingMonomialWithBotLT`, and `leadingMonomialWithBot` in the order hypothesis; use `h_g_ne_zero` and `hf` to extract `m.degree f ≺[m] m.degree g`, then apply `MonomialOrder.coeff_eq_zero_of_lt` with `d := m.degree g`.

## Review Gate Checklist

- [x] Source document, instructions, skeletons, preflight context, and manifest read by drafting pass.
- [x] Local/Mathlib search performed before declaration selection.
- [x] Blueprint placeholders replaced with declaration names, source locator, dependencies, statement-fidelity notes, and source proof notes.
- [x] Root project module imports the generated target path through `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Manual needs-review audit stamped every source entry on 2026-06-05.
- [x] Manual needs-review audit checked that the compiled Lean declaration/proof still matches the source statement and proof notes.
