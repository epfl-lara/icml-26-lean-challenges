# Formalization Blueprint: `algebra/L2/alg_grob_L2_022`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`
  - Defines `monomialSet` as the set of exponent-vector monomials appearing in at least one polynomial of a set.
  - States source lemma `monomial_set_union_distrib` with a `by sorry` proof placeholder for the later `/prove` workflow.
- Aggregator modules already import the target path:
  - `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
  - `ShadowBench.lean` imports `ShadowBench.Source`.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
```

The second direct import is used to represent the source qualifier that a monomial order on the exponent monoid is fixed.

## Suggested Search Modules

These modules/search terms were useful during planning but are not all forced into the Lean import block:

- `MvPolynomial.support` in `Mathlib.Algebra.MvPolynomial.Basic`
- `MonomialOrder` in `Mathlib.Data.Finsupp.MonomialOrder`
- `Set.mem_union`, set extensionality, and bounded-exists simplification facts from the set lattice API
- `Finset.mem_union` was inspected because the skeletons used `Finset`, but the final statement uses `Set` plus finiteness hypotheses to avoid decidable-equality artifacts.

## Required Names

- `monomial_set_union_distrib`

## Source Inventory

### S1. Lemma `monomial_set_union_distrib`

- Source locator: `docs/source.tex`, the named block beginning `Lemma (monomial_set_union_distrib)`.
- Source title/description: "Commutativity of union and monomial set".
- Complete source statement:

  > Let $F, G \subseteq R[\sigma]$ be some finite subsets of multivariate polynomials, where $\sigma$ is a set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a commutative semiring. Let $\mathrm{Mon}(F)$ be the entire set of monomials in some $f \in F$. Then $\mathrm{Mon}(F) \cup \mathrm{Mon}(G) = \mathrm{Mon}(F \cup G)$.

- Complete source proof text:

  > Denote by $\mathrm{Mon}(f)$ for $f \in R[\sigma]$ the set of monomials in $f$. Then $\mathrm{Mon}(F) = \bigcup_{f \in F} \mathrm{Mon}(f)$. Using this, we obtain
  > $$
  > \begin{aligned}
  > \mathrm{Mon}(F \cup G)
  > &= \bigcup_{f \in F \cup G} \mathrm{Mon}(f) \\
  > &= \bigcup_{f \in F}  \mathrm{Mon}(f) \cup \bigcup_{f \in G} \mathrm{Mon}(f) \\
  > &= \mathrm{Mon}(F) \cup \mathrm{Mon}(G).
  > \end{aligned}
  > $$

- Planned Lean declarations:
  - Companion definition `monomialSet`.
  - Source theorem `monomial_set_union_distrib`.
- Planned Lean statement:

  ```lean
  def monomialSet {R : Type*} [CommSemiring R] {σ : Type*}
      (S : Set (MvPolynomial σ R)) : Set (σ →₀ ℕ) :=
    {m | ∃ f ∈ S, m ∈ f.support}

  theorem monomial_set_union_distrib (R : Type*) [CommSemiring R] (σ : Type*)
      (order : MonomialOrder σ) (F G : Set (MvPolynomial σ R))
      (hF : F.Finite) (hG : G.Finite) :
      monomialSet F ∪ monomialSet G = monomialSet (F ∪ G) := by
    sorry
  ```

- Skeleton candidate used: Skeletons 1, 2, and 3 supplied the required theorem name and suggested representing finite collections explicitly. Their set element type was corrected from `MvPolynomial σ R` to `σ →₀ ℕ`, because `MvPolynomial.support` contains exponent-vector monomials. Skeleton 4 was malformed and was not adopted. The final statement uses `Set (MvPolynomial σ R)` with `F.Finite` and `G.Finite`, instead of `Finset`, to match the source wording `F, G \subseteq R[\sigma]` and avoid introducing a decidable-equality side condition for polynomial finset union. The unnecessary `[Fintype σ]` assumption from the candidates was omitted because the source does not say the variable-symbol type is finite and Mathlib supports arbitrary variable types for multivariate polynomials.
- Dependencies:
  - `MvPolynomial.support`, whose members are exponent vectors `σ →₀ ℕ`.
  - `Set (MvPolynomial σ R)` plus hypotheses `F.Finite` and `G.Finite` for finite subsets of polynomials.
  - `MonomialOrder σ` to record the source's fixed monomial-order context, although the union identity itself does not inspect that order.
  - Future proof should use `Set.ext`, unfold `monomialSet`, and split membership in `F ∪ G` using `simp`/`Set.mem_union`.
- Formal statement review:
  - The Lean definition `monomialSet S` formalizes "the entire set of monomials in some `f ∈ S`" as the set of support exponent vectors appearing in a member polynomial.
  - The theorem uses `Set (MvPolynomial σ R)` with finite-set hypotheses for the source's finite subsets of `R[σ]`.
  - The theorem conclusion preserves the source orientation `Mon(F) ∪ Mon(G) = Mon(F ∪ G)`.
  - The fixed monomial order is present as the parameter `order : MonomialOrder σ`; it is intentionally unused in the conclusion, matching the source proof's irrelevance of the order.
- Source qualifiers:
  - Mathematical object class: finite subsets of multivariate polynomials over a commutative semiring.
  - Quantifier order: `R`, semiring structure, variable-symbol type `σ`, fixed monomial order, subsets `F` and `G`, then finiteness witnesses for `F` and `G`.
  - Parameter domain: `F G : Set (MvPolynomial σ R)` with `hF : F.Finite` and `hG : G.Finite`.
  - Output codomain: equality of sets of monomial exponent vectors, `Set (σ →₀ ℕ)`.
  - Equality/image condition: monomials occurring in either `F` or `G` are exactly the monomials occurring in `F ∪ G`.
  - Side conditions: fixed monomial order on `σ`; finiteness of `F` and `G`; no finiteness assumption on `σ`.
  - Follow-on claims: none beyond the equality.
- Lean coverage:
  - `R` and `[CommSemiring R]` cover the coefficient semiring.
  - `σ : Type*` covers the variable-symbol set.
  - `order : MonomialOrder σ` covers the fixed monomial-order qualifier.
  - `F G : Set (MvPolynomial σ R)` with `hF : F.Finite` and `hG : G.Finite` covers finite subsets of multivariate polynomials.
  - `monomialSet` covers `Mon` as support membership over members of a subset.
  - `monomial_set_union_distrib` covers the source equality with the same orientation.
- Scope changes:
  - Monomials are represented by Mathlib support exponents `σ →₀ ℕ`, not by polynomial terms with coefficients. This is the standard representation used by `MvPolynomial.support`; coefficients are irrelevant to the source's set-of-monomials operation.
  - The source phrase "finite subsets" is encoded as a `Set` with finiteness hypotheses instead of a `Finset`; this avoids an extra decidable-equality assumption and keeps set union as the literal source operation.
  - No `[Fintype σ]` assumption is included, avoiding an extra restriction absent from the source.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes:
  - Prove by extensionality on a monomial exponent vector `m`.
  - After unfolding `monomialSet`, membership in the left side is `(∃ f ∈ F, m ∈ f.support) ∨ (∃ f ∈ G, m ∈ f.support)`.
  - Membership in the right side is `∃ f ∈ F ∪ G, m ∈ f.support`, and `f ∈ F ∪ G` reduces to `f ∈ F ∨ f ∈ G`.
  - The proof should be a short `constructor` proof or a `simp [monomialSet, and_or_left]` style proof after extensionality; do not change the theorem statement during proving without a new statement/source review.

## Formalization Checklist

- [x] Source document and preflight manifest read.
- [x] Candidate skeletons and instructions read.
- [x] Local/Mathlib search performed before drafting.
- [x] Blueprint source inventory contains declaration names, source locators, statement-fidelity notes, source proof text, and prover notes.
- [x] Root project module imports the generated target module path.
- [ ] Statement verification approved by an independent review pass.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
