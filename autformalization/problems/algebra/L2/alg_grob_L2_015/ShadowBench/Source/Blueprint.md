# Formalization Blueprint: `algebra/L2/alg_grob_L2_015`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source and Preflight Read

- Source document inspected: `docs/source.tex`.
- Preflight manifest read: `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- Planner context read: `.epflemma/workflow-state/formalization/docs-source/context.md`.
- Nearby support files read: `docs/instructions.md`, `docs/skeletons/README.md`, and `docs/skeletons/Skeleton1.lean` through `Skeleton4.lean`.
- Bibliography/PDF/figure support files: none listed in the manifest.
- Deterministic source inventory: one named lemma, `lm'_add_lt_of_both_lm'_lt`; no LaTeX theorem environments or labels were detected by preflight, so the plain-text lemma block is the source locator.

## Generated File Layout

- Final organization decision: stay single-file. The generated scope has only one bridge definition and one source lemma, so a split would add import overhead without improving structure.
- `ShadowBench/Source/Main.lean`: contains the local source-notation bridge `leadingMonomial` and the source lemma skeleton `lm'_add_lt_of_both_lm'_lt`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the generated target module is covered by the project root.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

## Import Plan

```lean
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
```

## Suggested Search Modules

These are search/proof hints, not direct imports unless the prover later needs them:

- `Mathlib.Data.Finsupp.MonomialOrder`
- `Mathlib.RingTheory.MvPolynomial.Groebner`
- `Mathlib.RingTheory.MvPolynomial.MonomialOrder`

Useful searched declarations include `MonomialOrder.degree`, `MonomialOrder.degree_add_le`, `MonomialOrder.degree_le_iff`, `MonomialOrder.degree_mem_support`, and the scoped comparison notation `c ≺[m] d` / `c ≼[m] d`.

## Required Names

- `lm'_add_lt_of_both_lm'_lt`

## Definitions and Representation Bridges

### `leadingMonomial`

- Lean declaration: `leadingMonomial`
- Purpose: explicit source-notation bridge for `LM(f)`.
- Lean type: for `m : MonomialOrder σ` and `f : MvPolynomial σ R`, `leadingMonomial m f : σ →₀ ℕ`.
- Definition: `leadingMonomial m f := m.degree f`.
- Fidelity note: Mathlib names the exponent vector of the leading monomial `m.degree f`. The source writes `LM(f)` for the leading monomial under a fixed monomial order. This bridge records that the formal theorem compares leading monomial exponent vectors; coefficients/leading terms are not part of the source statement.
- Construction status: implemented directly, no proof or construction gap.

## Statement Inventory

### Lemma `lm'_add_lt_of_both_lm'_lt`

- Planned Lean declaration: `lm'_add_lt_of_both_lm'_lt`
- Companion bridge declaration: `leadingMonomial`
- Source locator: `docs/source.tex`, plain-text lemma block headed `Lemma (lm'_add_lt_of_both_lm'_lt) Leading monomial of addition (nonzero case)`.
- Source statement:
  "Let `f_1, f_2, g ∈ R[σ]` be nonzero multivariate polynomials, and suppose that the sum `f_1 + f_2` is also nonzero. Here, `σ` is a set of variable symbols over which a monomial order `>` is fixed, and `R` is a commutative semiring. Given `LM(f_1) < LM(g)` and `LM(f_2) < LM(g)`, we have `LM(f_1 + f_2) < LM(g)`."
- Skeleton candidate used: `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` all suggested the required theorem name, nonzero assumptions, and the same high-level signature shape. They were not copied verbatim because they use `MvPolynomial.leadingMonomial`, which search did not find in Mathlib. `Skeleton4.lean` also has a malformed duplicate `:= by sorry`. The final statement uses the Mathlib `MonomialOrder.degree` bridge instead.
- Dependencies:
  - `Mathlib.RingTheory.MvPolynomial.MonomialOrder`
  - `MonomialOrder` and scoped notation `≺[m]`
  - `MvPolynomial σ R`
  - bridge definition `leadingMonomial`
- Source qualifiers:
  - Mathematical object class: multivariate polynomials over variables `σ` and coefficient semiring `R`.
  - Parameter domain: `R` is a commutative semiring; `σ` is a type of variables; `m : MonomialOrder σ` is the fixed monomial order.
  - Quantifier order: choose `R`, its `CommSemiring` instance, `σ`, a monomial order `m`, and polynomials `f₁ f₂ g`.
  - Side conditions: `f₁ ≠ 0`, `f₂ ≠ 0`, `g ≠ 0`, and `f₁ + f₂ ≠ 0`.
  - Hypotheses: `LM(f₁) < LM(g)` and `LM(f₂) < LM(g)` in the fixed monomial order.
  - Output codomain/equality condition: strict comparison of leading monomial exponent vectors; no coefficient equality or leading-term equality is claimed.
  - Follow-on claims: none.
- Lean coverage:
  - `R : Type*` with `[CommSemiring R]` covers the source coefficient semiring.
  - `σ : Type*` covers the set/type of variable symbols.
  - `(m : MonomialOrder σ)` covers the fixed monomial order.
  - `(f₁ f₂ g : MvPolynomial σ R)` covers `f_1, f_2, g ∈ R[σ]`.
  - `(hf₁_nonzero : f₁ ≠ 0)`, `(hf₂_nonzero : f₂ ≠ 0)`, `(hg_nonzero : g ≠ 0)`, and `(hsum_nonzero : f₁ + f₂ ≠ 0)` cover the nonzero side conditions.
  - `leadingMonomial m f₁ ≺[m] leadingMonomial m g` and `leadingMonomial m f₂ ≺[m] leadingMonomial m g` cover the two source inequalities.
  - The conclusion `leadingMonomial m (f₁ + f₂) ≺[m] leadingMonomial m g` covers the source conclusion.
- Scope changes:
  - Explicit representation bridge: Lean represents `LM(f)` by the exponent vector `m.degree f : σ →₀ ℕ`, exposed as `leadingMonomial m f`. This is a representation choice, not a mathematical weakening.
  - No source side condition is omitted. The nonzero assumptions may be unnecessary for the Mathlib proof because `m.degree 0` is defined, but they are retained for source fidelity.
- Formal statement review:
  - The final Lean declaration preserves the source's coefficient class, polynomial class, fixed monomial order, nonzero hypotheses, two strict leading-monomial hypotheses, and strict leading-monomial conclusion.
  - The statement avoids the invalid skeleton name `MvPolynomial.leadingMonomial` and records the intended `LM` interpretation with `leadingMonomial`.
  - The theorem does not assert a stronger equality such as `LM(f₁ + f₂) = max (LM f₁) (LM f₂)` and does not drop the source nonzero assumptions.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  "It is assumed that every monomial in `f_1` or `f_2` is less than `LM(g)`, under the fixed monomial order. Since the monomials in `f_1 + f_2` must be in at least one of `f_1` and `f_2`, those monomials must still be less than `LM(g)`, hence the inequality."
- Proof sketch:
  Every support monomial of `f₁ + f₂` comes from the support of `f₁` or `f₂`. Since the leading monomials of both summands are strictly below `LM(g)`, all support monomials of both summands are below `LM(g)`; hence the largest support monomial of the sum is also below `LM(g)`.
- Prover notes:
  - Unfold `leadingMonomial` to `m.degree`.
  - `m.degree_add_le` gives `m.toSyn (m.degree (f₁ + f₂)) ≤ m.toSyn (m.degree f₁) ⊔ m.toSyn (m.degree f₂)`.
  - Use the two strict hypotheses to show the supremum on the right is `< m.toSyn (m.degree g)`, then finish with transitivity.
  - The assumptions `hf₁_nonzero`, `hf₂_nonzero`, `hg_nonzero`, and `hsum_nonzero` are included for source fidelity and may not be needed by the short proof.

## Handoff Notes

- Final organization verification: passed with `lean_verify(mode=project)` after keeping the single-file layout. The remaining warning is the intentional theorem `sorry` for the later proof workflow.
- No additional generated Lean modules were introduced; root imports already cover `ShadowBench.Source.Main` through `ShadowBench.Source`.
- Suggested proof command: `/prove ShadowBench/Source/Main.lean lm'_add_lt_of_both_lm'_lt`.
