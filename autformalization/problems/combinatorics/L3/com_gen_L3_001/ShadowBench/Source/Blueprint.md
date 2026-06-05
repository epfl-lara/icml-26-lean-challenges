# ShadowBench combinatorics/L3/com_gen_L3_001 formalization blueprint

- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.
- Source document: `docs/source.tex`
- Target Lean file: `ShadowBench/Source/Main.lean`
- Source kind: LaTeX
- Problem id: combinatorics/L3/com_gen_L3_001

## Generated File Layout

The generated formalization stays in one Lean file, `ShadowBench/Source/Main.lean`.  The parent module `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, and the root module `ShadowBench.lean` imports `ShadowBench.Source`, so a plain project build reaches the generated formalization.

## Import Plan

```lean
import Mathlib.Combinatorics.Matroid.Minor.Contract
```

This is the only direct Lean import for `ShadowBench/Source/Main.lean`.  It provides Mathlib's matroid contraction definition, deletion, duality, independence, bases, coindependence, and cocircuit vocabulary used by the drafted statements.

## Suggested Search Modules

These are non-gating proof-search hints, not additional direct imports for the target file.

- `Mathlib.Combinatorics.Matroid.Minor.Delete`
- `Mathlib.Combinatorics.Matroid.Dual`
- `Mathlib.Combinatorics.Matroid.Circuit`
- `Mathlib.Combinatorics.Matroid.Basis`

## Skeleton Usage

The source labels and names follow `docs/source.tex` and the ShadowBench skeleton suggestions.  The final Lean statements were checked against the source text rather than copied blindly from a skeleton.  Existing Mathlib declarations in `Mathlib.Combinatorics.Matroid.Minor.Contract` supply the intended semantics; the generated file wraps the source names at root level to avoid clashing with Mathlib names such as `Matroid.contract_ground` and `Matroid.Indep.contract_indep_iff`.

## Representation Decisions

- The source writes a matroid on a ground set `E`; Lean represents the ground set as the field `M.E` of a `Matroid α`.
- The source notation `M / C` is represented by `Matroid.contract M C`.
- The source notation `M \setminus X` is represented by `Matroid.delete M X`.
- The source notation `M^*` is represented by `Matroid.dual M`.
- Conditions such as `X ∩ C = ∅` are represented by `Disjoint X C`, the standard Lean proposition equivalent to empty intersection for sets.
- The source's subset-of-ground-set hypotheses are retained as explicit hypotheses when the text states them, even when the corresponding Mathlib theorem is naturally stronger.

## Source Statement Inventory

### line-17

- Source title: `contract`
- Source kind: definition
- Source locator: `docs/source.tex` lines 17-23
- Planned Lean declarations: `contract`
- Dependencies: Mathlib definition `Matroid.contract`; semantic bridge to `Matroid.dual` and `Matroid.delete` supplied by Mathlib.
- Source statement: Let `M` be a matroid on a ground set `E`, and let `C ⊆ E`.  The contraction of `C` from `M`, denoted `M / C`, is defined by `M / C := (M^* \setminus C)^*`.
- Complete source proof text: Definition only; no proof appears in the source.
- Source qualifiers: mathematical object class is matroids; parameters are a matroid `M` and a set `C` lying in the ground set; output codomain is a matroid on the same element type; defining equality is contraction as dual of deletion in the dual.
- Lean coverage: The Lean declaration `contract` is a definition returning `Matroid.contract M C`.  Mathlib's `Matroid.contract` is the contraction operation with the source's dual-delete-dual semantics.
- Scope changes: None for the operation.  The ambient ground set `E` is represented as `M.E` rather than as a separate parameter.
- Formal statement review: The definition is a bridge declaration for the source notation and uses the same object class and codomain as the source.  The source subset condition is a domain convention for the operation; later lemmas record it explicitly when stated.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Definition only.  Use Mathlib's `Matroid.contract` and its dual/delete lemmas (`Matroid.dual_contract`, `Matroid.dual_delete_dual`) for later proofs.

### line-25

- Source title: `contract_ground`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 25-36
- Planned Lean declarations: `contract_ground`
- Dependencies: `contract`; Mathlib facts around `Matroid.contract_ground`, deletion ground sets, and dual ground sets.
- Source statement: For any matroid `M` and set `C ⊆ E`, `E(M / C) = E(M) \setminus C`.
- Complete source proof text: By definition `M / C = (M^* \setminus C)^*`.  Taking ground sets and using the corresponding facts for deletion and duality yields `E(M / C) = E(M) \setminus C`.
- Source qualifiers: object class is matroids; quantifiers are `M` then `C`; parameter domain includes `C ⊆ E(M)`; equality condition is the ground set of the contraction equals the original ground set minus `C`; no follow-on claim.
- Lean coverage: `contract_ground` states `(Matroid.contract M C).E = M.E \ C` with an explicit source-domain hypothesis `hC : C ⊆ M.E`.
- Scope changes: None.  The statement keeps the subset hypothesis although Mathlib's core result may not need it.
- Formal statement review: The Lean statement matches the source after translating `E(M)` to `M.E` and `/` to `Matroid.contract`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Source proof unfolds contraction as dual-delete-dual and then rewrites ground sets.  Mathlib search found `Matroid.contract_ground`; that theorem should likely close the proof immediately.

### line-38

- Source title: `dual_delete_dual`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 38-50
- Planned Lean declarations: `dual_delete_dual`
- Dependencies: `contract`; Mathlib duality lemmas `Matroid.dual_contract` and `Matroid.dual_delete`/`Matroid.dual_delete_dual`.
- Source statement: For any matroid `M` and set `X ⊆ E`, `(M / X)^* = M^* \setminus X` and `(M \setminus X)^* = M^* / X`.
- Complete source proof text: Both identities follow directly from the definition of contraction `M / X := (M^* \setminus X)^*` and the involutivity of matroid duality.
- Source qualifiers: object class is matroids; quantifiers are `M` then `X`; parameter domain includes `X ⊆ E(M)`; output is a pair of matroid equalities; equality conditions are dual of contraction equals deletion in the dual, and dual of deletion equals contraction in the dual.
- Lean coverage: `dual_delete_dual` states the two equalities as a conjunction using `Matroid.dual`, `Matroid.contract`, and `Matroid.delete`, with explicit source-domain hypothesis `hX : X ⊆ M.E`.
- Scope changes: None.  The two displayed source equalities are grouped into one conjunctive theorem with the source label.
- Formal statement review: The Lean conjunction covers both displayed equalities exactly under the source subset-of-ground-set domain.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Source proof is definitional plus dual involutivity.  Mathlib has `Matroid.dual_contract` and `Matroid.dual_delete`; use those names or simp with contraction definitions.

### line-52

- Source title: `contract_contract`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 52-68
- Planned Lean declarations: `contract_contract`
- Dependencies: `contract`; Mathlib contraction composition and commutativity lemmas such as `Matroid.contract_contract` and `Matroid.contract_comm`.
- Source statement: For any matroid `M` and sets `C₁, C₂ ⊆ E`, `M / C₁ / C₂ = M / (C₁ ∪ C₂)`.  In particular, `M / C₁ / C₂ = M / C₂ / C₁`.
- Complete source proof text: Using the definition of contraction via duality, iterated contraction corresponds to iterated deletion in the dual matroid.  Since deletion distributes over unions, the result follows.  Commutativity is immediate from the commutativity of union.
- Source qualifiers: object class is matroids; quantifiers are `M`, `C₁`, `C₂`; parameter domain includes both sets lying in `E(M)`; first equality is associativity/composition over union; follow-on claim is commutativity of two contractions.
- Lean coverage: `contract_contract` states both the composition equality and the follow-on commutativity equality as a conjunction, using explicit hypotheses `hC₁ : C₁ ⊆ M.E` and `hC₂ : C₂ ⊆ M.E`.
- Scope changes: None.  The source's “in particular” is included as the second conjunct rather than split into a second declaration.
- Formal statement review: The Lean theorem covers the full displayed source lemma after translating the notation and retaining the source set-domain hypotheses.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Rewrite contractions into deletions in the dual, apply deletion-over-union, then use union commutativity.  Mathlib search found `Matroid.contract_contract` and `Matroid.contract_comm`.

### line-70

- Source title: `contract_empty`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 70-80
- Planned Lean declarations: `contract_empty`
- Dependencies: `contract`; Mathlib empty deletion/contraction simplification facts.
- Source statement: For any matroid `M`, `M / ∅ = M`.
- Complete source proof text: This follows from the definition of contraction and the fact that deleting the empty set has no effect on a matroid.
- Source qualifiers: object class is matroids; quantifier is `M`; contracted set is empty; equality condition is contraction by the empty set gives the original matroid; no side conditions.
- Lean coverage: `contract_empty` states `Matroid.contract M ∅ = M` for any `Matroid α`.
- Scope changes: None.
- Formal statement review: The Lean statement is a direct translation of the source statement with `/` replaced by `Matroid.contract`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Use the contraction definition and the fact that deletion of `∅` is the identity.  Mathlib may have a simp lemma for `Matroid.contract_empty` or close by simp.

### line-82

- Source title: `contract_eq_contract_iff`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 82-94
- Planned Lean declarations: `contract_eq_contract_iff`
- Dependencies: `contract`; Mathlib theorem `Matroid.contract_eq_contract_iff`; deletion equality criterion in the dual matroid.
- Source statement: For any matroid `M` and sets `C₁, C₂ ⊆ E`, `M / C₁ = M / C₂ ↔ C₁ ∩ E(M) = C₂ ∩ E(M)`.
- Complete source proof text: Using the dual characterization of contraction, the statement reduces to the corresponding criterion for equality of deletions in the dual matroid.
- Source qualifiers: object class is matroids; quantifiers are `M`, `C₁`, `C₂`; parameter domain includes both sets lying in `E(M)`; proposition is an iff; equality/image condition compares contractions to equality of intersections with the ground set.
- Lean coverage: `contract_eq_contract_iff` states `Matroid.contract M C₁ = Matroid.contract M C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E`, with explicit source-domain hypotheses for `C₁` and `C₂`.
- Scope changes: None.  The intersection form is retained even though the subset hypotheses make it equivalent to `C₁ = C₂`.
- Formal statement review: The Lean statement matches the source iff and keeps the displayed intersection with the matroid ground set.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Translate contraction equality to deletion equality in the dual.  Mathlib search found `Matroid.contract_eq_contract_iff`.

### line-96

- Source title: `coindep_contract_iff`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 96-109
- Planned Lean declarations: `coindep_contract_iff`
- Dependencies: `contract`; Mathlib dual/coindependence facts and deletion independence characterization.
- Source statement: Let `M` be a matroid, `C ⊆ E(M)`, and `X ⊆ E(M)`.  Then `X` is coindependent in `M / C` iff `X` is coindependent in `M` and `X ∩ C = ∅`.
- Complete source proof text: This follows by rewriting coindependence in terms of independence in the dual matroid and applying the characterization of deletion.
- Source qualifiers: object class is matroids; quantifiers are `M`, `C`, `X`; parameter domains include `C ⊆ E(M)` and `X ⊆ E(M)`; proposition is an iff; side condition is disjointness of `X` and `C`.
- Lean coverage: `coindep_contract_iff` states `(Matroid.contract M C).Coindep X ↔ M.Coindep X ∧ Disjoint X C`, with the source-domain hypotheses `hC` and `hX`.
- Scope changes: None.  `Disjoint X C` is used for `X ∩ C = ∅`.
- Formal statement review: The Lean statement is faithful to the source after translating coindependence to Mathlib's `Coindep` predicate and empty intersection to `Disjoint`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Rewrite `Coindep` through dual independence, convert contraction to deletion in the dual, and apply the deletion characterization for independence/coindependence.

### line-111

- Source title: `contract_isCocircuit_iff`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 111-120
- Planned Lean declarations: `contract_isCocircuit_iff`
- Dependencies: `coindep_contract_iff`; Mathlib cocircuit definition `Matroid.IsCocircuit` and dual/circuit facts.
- Source statement: Let `M` be a matroid and `C ⊆ E(M)`.  A set `K` is a cocircuit of `M / C` iff `K` is a cocircuit of `M` and `K ∩ C = ∅`.
- Complete source proof text: This is an immediate consequence of the previous lemma together with the definition of cocircuits in terms of coindependence.
- Source qualifiers: object class is matroids; quantifiers are `M`, `C`, `K`; parameter domain includes `C ⊆ E(M)`; proposition is an iff; side condition is disjointness of cocircuit `K` from `C`.
- Lean coverage: `contract_isCocircuit_iff` states `(Matroid.contract M C).IsCocircuit K ↔ M.IsCocircuit K ∧ Disjoint K C`, with explicit source-domain hypothesis `hC : C ⊆ M.E`.
- Scope changes: None.  `Disjoint K C` represents `K ∩ C = ∅`.
- Formal statement review: The Lean theorem matches the source cocircuit iff using Mathlib's cocircuit predicate.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Use `coindep_contract_iff` and unfold/translate cocircuit as a circuit in the dual or via cocircuit/coindependence characterizations.

### line-122

- Source title: `Indep.contract_isBase_iff`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 122-136
- Planned Lean declarations: `Indep.contract_isBase_iff`
- Dependencies: Mathlib theorem `Matroid.Indep.contract_isBase_iff`; basis and independence predicates.
- Source statement: Let `M` be a matroid and let `I ⊆ E(M)` be independent.  A set `B` is a basis of `M / I` iff `B ∪ I` is a basis of `M` and `B ∩ I = ∅`.
- Complete source proof text: Using duality, the statement reduces to the corresponding characterization of bases under deletion.  Translating back yields the claim.
- Source qualifiers: object class is matroids; quantifiers are `M`, independent set `I`, and set `B`; parameter domain for `I` is encoded by `M.Indep I`; proposition is an iff; conditions are base of the union in `M` and disjointness from `I`.
- Lean coverage: `Indep.contract_isBase_iff` is a root-level source wrapper taking `hI : M.Indep I` and stating `(Matroid.contract M I).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B I`.
- Scope changes: None.  The source phrase `I ⊆ E(M) is independent` is represented by `M.Indep I`, which includes membership in the matroid ground set in Mathlib.
- Formal statement review: The Lean statement matches the source basis characterization, including the source order `B ∪ I`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Use duality and the deletion basis characterization.  Mathlib search found `Matroid.Indep.contract_isBase_iff`, which likely matches the statement or needs only commutativity/disjointness normalization.

### line-138

- Source title: `Indep.contract_indep_iff`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 138-153
- Planned Lean declarations: `Indep.contract_indep_iff`
- Dependencies: `Indep.contract_isBase_iff`; Mathlib theorem `Matroid.Indep.contract_indep_iff`.
- Source statement: Let `M` be a matroid and let `I ⊆ E(M)` be independent.  For any set `J ⊆ E(M)`, `J` is independent in `M / I` iff `J ∩ I = ∅` and `J ∪ I` is independent in `M`.
- Complete source proof text: A set is independent if and only if it is contained in a basis.  Applying the previous lemma on bases yields the equivalence.
- Source qualifiers: object class is matroids; quantifiers are `M`, independent set `I`, and set `J`; parameter domains are `M.Indep I` and `J ⊆ M.E`; proposition is an iff; side conditions are disjointness from `I` and independence of `J ∪ I` in `M`.
- Lean coverage: `Indep.contract_indep_iff` takes `hI : M.Indep I` and `hJ : J ⊆ M.E`, and states `(Matroid.contract M I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I)`.
- Scope changes: None.  `Disjoint J I` represents `J ∩ I = ∅`.
- Formal statement review: The Lean theorem faithfully retains the source hypotheses and the source order of the union `J ∪ I`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Prove via basis extension and `Indep.contract_isBase_iff`, or use Mathlib's `Matroid.Indep.contract_indep_iff` and normalize union/disjointness.

### line-155

- Source title: `IsNonloop.contractElem_indep_iff`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 155-170
- Planned Lean declarations: `IsNonloop.contractElem_indep_iff`
- Dependencies: `Indep.contract_indep_iff`; Mathlib nonloop facts showing `{e}` is independent when `e` is a nonloop.
- Source statement: Let `M` be a matroid and let `e` be a non-loop element of `M`.  For any set `I`, `I` is independent in `M / {e}` iff `e ∉ I` and `I ∪ {e}` is independent in `M`.
- Complete source proof text: This is the specialization of the previous lemma to the case `I = {e}`, using that `e` is independent.
- Source qualifiers: object class is matroids; quantifiers are `M`, element `e`, and set `I`; side condition is `M.IsNonloop e`; proposition is an iff; conditions are element nonmembership and independence of adjoining `e`.
- Lean coverage: `IsNonloop.contractElem_indep_iff` takes `he : M.IsNonloop e` and states `(Matroid.contract M {e}).Indep I ↔ e ∉ I ∧ M.Indep (I ∪ {e})`.
- Scope changes: None.  The non-loop hypothesis supplies the singleton independence/ground-membership content used by the source proof.
- Formal statement review: The Lean statement is the singleton specialization of the previous source lemma and matches the displayed iff.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Instantiate `Indep.contract_indep_iff` at `{e}`.  Use the Mathlib nonloop-to-singleton-independent lemma and simplify `Disjoint I {e}` to `e ∉ I`.

### line-172

- Source title: `IsBasis.contract_eq_contract_delete`
- Source kind: lemma
- Source locator: `docs/source.tex` lines 172-185
- Planned Lean declarations: `IsBasis.contract_eq_contract_delete`
- Dependencies: contraction composition/deletion commutation; Mathlib basis-of-set predicate `M.IsBasis I X` and related contraction lemmas.
- Source statement: Let `M` be a matroid, `X ⊆ E(M)`, and let `I` be a basis of `X`.  Then `M / X = M / I \setminus (X \setminus I)`.
- Complete source proof text: Decompose `X` as the disjoint union of the basis `I` and the remaining elements `X \setminus I`.  Contracting `X` is equivalent to contracting `I` and deleting the remaining elements, which gives the stated equality.
- Source qualifiers: object class is matroids; quantifiers are `M`, set `X`, and basis `I` of `X`; parameter domain `X ⊆ E(M)` is encoded by `M.IsBasis I X`; equality condition relates contraction by `X` to contraction by a basis followed by deletion of `X \ I`.
- Lean coverage: `IsBasis.contract_eq_contract_delete` takes `hI : M.IsBasis I X` and states `Matroid.contract M X = Matroid.delete (Matroid.contract M I) (X \ I)`.
- Scope changes: None.  The basis-of-`X` hypothesis in Mathlib carries the subset and independence information from the source.
- Formal statement review: The Lean theorem is a direct translation of the displayed equality using `Matroid.contract` and `Matroid.delete`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Split `X` into `I` and `X \ I`, use contraction by a spanning/basis subset, then delete the residual elements.  Search Mathlib for `IsBasis.contract_eq_contract_delete`, contraction/delete commutation, and basis contraction lemmas.

## Handoff Checklist

- [x] Read `docs/source.tex` and deterministic preflight extraction.
- [x] Read ShadowBench instructions and skeleton suggestions.
- [x] Search local/Mathlib facts before drafting Lean names and statements.
- [x] Draft source-mapped Lean declarations with source proof/prover notes in doc comments.
- [ ] Run independent statement/source verification review and apply corrections.
- [ ] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.

## Prover Queue Notes

After independent statement/source review approves the inventory, the expected theorem queue is:

1. `contract_ground`
2. `dual_delete_dual`
3. `contract_contract`
4. `contract_empty`
5. `contract_eq_contract_iff`
6. `coindep_contract_iff`
7. `contract_isCocircuit_iff`
8. `Indep.contract_isBase_iff`
9. `Indep.contract_indep_iff`
10. `IsNonloop.contractElem_indep_iff`
11. `IsBasis.contract_eq_contract_delete`

Do not start this proof queue until a separate statement/source verification pass has checked the source locators, statement fidelity, and doc-comment proof notes.
