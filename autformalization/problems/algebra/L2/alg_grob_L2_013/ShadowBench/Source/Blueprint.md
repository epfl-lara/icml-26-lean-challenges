# Formalization Blueprint: `algebra/L2/alg_grob_L2_013`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench.lean` imports `ShadowBench.Source`.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench/Source/Main.lean` contains the source-backed lemma `lm_add_le_of_both_lm_le_mon`.

No additional file split is currently needed because the source document has one lemma and no auxiliary definitions are required beyond Mathlib's existing monomial-order API.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
```

These are the direct imports used by `ShadowBench/Source/Main.lean`. The third import is needed for `MonomialOrder.degree`, `MonomialOrder.leadingTerm`, and `MonomialOrder.degree_add_le`.

## Suggested Search Modules

- `Mathlib.RingTheory.MvPolynomial.MonomialOrder`: search around `MonomialOrder.degree_add_le`, `MonomialOrder.degree_monomial`, and `MonomialOrder.leadingTerm_monomial` for the proof.
- `Mathlib.Data.Finsupp.MonomialOrder`: search around scoped notation `c ≼[m] d` and `c ≺[m] d` if order notation elaboration is unclear.

## Required Names

- `lm_add_le_of_both_lm_le_mon`

## Statement Inventory

### Source lemma: `lm_add_le_of_both_lm_le_mon`

- Planned Lean declaration: `lm_add_le_of_both_lm_le_mon`
- Source locator: `docs/source.tex`, lines 17-23
- Source kind: lemma
- Source title/description: "Upper bound of the leading monomial of addition"
- Skeleton candidate used: Skeletons 1, 2, and 3 all suggested the required name and a two-polynomial bounded-leading-monomial shape. Their use of `MvPolynomial.leadingMonomial` was not adopted because Mathlib's monomial-order API represents the leading monomial exponent as `m.degree f`. Skeleton4 was rejected as malformed because it has an extra trailing `:= by sorry`.
- Dependencies: `MvPolynomial`, `MonomialOrder`, scoped notation `≼[m]`, `MonomialOrder.degree`, and, for the later proof, `MonomialOrder.degree_add_le` plus `sup_le`.

#### Complete source statement

"Let $f_1, f_2 \in R[\sigma]$ be multivariate polynomials (which might be zero). Here, $\sigma$ is a set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a nontrivial commutative semiring. Given a monomial $x^\delta$ such that $\mathrm{LM}(f_1) \le x^\delta$ and $\mathrm{LM}(f_2) \le x^\delta$, we have $\mathrm{LM}(f_1 + f_2) \le x^\delta$."

#### Complete source proof text

"It suffices to take a polynomial $g \in R[\sigma]$ whose leading monomial is $\delta$. Such polynomial exists from $R \ne \{0\}$; in particular, $g$ can be taken as the monomial $cx^\delta$ for some $c \in R \setminus \{0\}$. Now we obtain the result from the same inequality for $f_1, f_2$ and $g$."

#### Source qualifiers

- Mathematical object class: multivariate polynomials `f₁ f₂ : MvPolynomial σ R` over variables `σ` and coefficients `R`.
- Variable domain: `σ : Type*` is arbitrary; the fixed monomial order is represented by `m : MonomialOrder σ`.
- Coefficient domain: `R : Type*` with `[CommSemiring R]` and `[Nontrivial R]`.
- Zero-polynomial allowance: both `f₁` and `f₂` may be zero.
- Monomial bound: the monomial `x^δ` is represented by its exponent vector `δ : σ →₀ ℕ`.
- Leading monomial representation: `LM(f)` is represented by the exponent vector `m.degree f`; Mathlib separately provides `m.leadingTerm f` for the coefficient-weighted monomial term.
- Order condition: `LM(f) ≤ x^δ` is represented as `m.degree f ≼[m] δ`, i.e. `m.toSyn (m.degree f) ≤ m.toSyn δ`.
- Quantifier order: the Lean declaration quantifies `σ`, `R`, typeclass assumptions, `m`, `f₁`, `f₂`, `δ`, then the two hypotheses and the conclusion.
- Output codomain: the conclusion is a proposition giving the same monomial-order bound for `f₁ + f₂`.

#### Lean coverage

The Lean statement covers the source lemma using Mathlib's canonical monomial-order degree API:

```lean
theorem lm_add_le_of_both_lm_le_mon {σ : Type*} {R : Type*}
    [CommSemiring R] [Nontrivial R] (m : MonomialOrder σ)
    (f₁ f₂ : MvPolynomial σ R) (δ : σ →₀ ℕ)
    (h₁ : m.degree f₁ ≼[m] δ) (h₂ : m.degree f₂ ≼[m] δ) :
    m.degree (f₁ + f₂) ≼[m] δ
```

This treats zero polynomials via Mathlib's definition `m.degree 0 = 0` and does not require extra decidable-equality assumptions on `σ`.

#### Scope changes

- The source's notation `LM(f)` is formalized as the exponent vector `m.degree f`, not as the full coefficient-bearing polynomial `m.leadingTerm f`. This is the intended bridge because the source compares `LM(f)` to the monomial `x^δ`, so only the exponent/monomial-order position is used.
- The source's fixed order written as `>` is represented by `m : MonomialOrder σ`; the non-strict comparison `≤` is represented by scoped notation `≼[m]`.
- The source proof introduces a monomial polynomial `g = c x^δ` to witness the bound. The Lean theorem statement does not introduce `g`, because Mathlib already has the more direct degree-of-addition lemma needed for the proof.

#### Formal statement review

- The theorem name matches the required source name exactly.
- The statement preserves the source assumptions `[CommSemiring R]` and `[Nontrivial R]`, even though the available Mathlib addition-degree bound itself does not need nontriviality.
- The statement explicitly includes an arbitrary fixed monomial order `m : MonomialOrder σ` rather than using an untracked order instance.
- The hypotheses and conclusion are expressed in terms of the same monomial-order comparison against the same `δ`.
- No coefficient-side claim about leading coefficients or cancellation behavior is added.

#### Source proof / prover notes

For the later prover pass, unfold the notation only if necessary. The proof should be a short order argument using Mathlib's addition bound:

```lean
  exact le_trans (m.degree_add_le (f := f₁) (g := f₂)) (sup_le h₁ h₂)
```

Here `m.degree_add_le` gives `m.toSyn (m.degree (f₁ + f₂)) ≤ m.toSyn (m.degree f₁) ⊔ m.toSyn (m.degree f₂)`, and `sup_le h₁ h₂` converts the two hypotheses into the desired upper bound by `m.toSyn δ`.

- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Verification Plan

- Draft readiness: `ShadowBench/Source/Main.lean` has been checked.
- Project readiness: `lake build` has passed.
- Manual needs-review audit passed on 2026-06-05.

## Proof Queue Handoff

The target theorem is already proof-complete. No prover handoff is currently needed; rerun only if the statement changes:

```text
/prove ShadowBench/Source/Main.lean lm_add_le_of_both_lm_le_mon
```
