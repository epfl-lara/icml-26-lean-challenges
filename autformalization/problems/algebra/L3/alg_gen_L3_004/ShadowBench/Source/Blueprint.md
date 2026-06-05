# Formalization Blueprint: `algebra/L3/alg_gen_L3_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Import Plan

```lean
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Tactic.TautoSet
```

The target file uses exactly the imports above. `Contract` is needed for Mathlib's contraction definition, dual/deletion notation, and existing contraction lemmas. `TautoSet` is part of the allowed starting import block and is also a transitive dependency of the Mathlib contraction file.

## Suggested Search Modules

These are proof-search hints only; they are not additional direct imports for the draft.

- `Mathlib.Combinatorics.Matroid.Minor.Contract`
- `Mathlib.Combinatorics.Matroid.Minor.Delete`
- `Mathlib.Combinatorics.Matroid.Dual`
- Search facts found before drafting: `Matroid.contract`, `Matroid.contract_ground`, `Matroid.dual_contract`, `Matroid.dual_delete`, `Matroid.contract_contract`, `Matroid.contract_comm`, `Matroid.contract_empty`, `Matroid.contract_eq_contract_iff`, `Matroid.coindep_contract_iff`, `Matroid.contract_isCocircuit_iff`, `Matroid.Indep.contract_isBase_iff`, `Matroid.Indep.contract_indep_iff`, `Matroid.IsNonloop.contractElem_indep_iff`, `Matroid.IsBasis.contract_eq_contract_delete`.

## Generated File Layout

- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so the generated target is covered by the root `ShadowBench` library build.
- `ShadowBench/Source/Main.lean` contains the source-backed definition `contract` and all source-backed theorem/lemma skeletons in one file. No split is currently useful because the source document is short and all declarations share the same matroid-contraction context.

## Global Formalization Choices

- The source phrase `E(M)` is formalized as Mathlib's matroid ground set `M.E`.
- The source notation `M / C` is formalized by the top-level wrapper `contract M C`; its body is Mathlib's dual-deletion definition `(M✶ ＼ C)✶`.
- Mathlib's contraction is total in the set argument `C : Set α`. The source often says `C ⊆ E(M)`; the theorem statements include such subset hypotheses where the source explicitly lists them. The definition itself follows Mathlib's total-domain convention, with outside-ground behavior controlled by `contract_eq_contract_iff`.
- Source claims using empty intersection are stated as `X ∩ C = ∅` or `B ∩ I = ∅` rather than replacing them with `Disjoint`, to preserve the source surface statement. Provers may use Mathlib lemmas stated with `Disjoint` and convert.
- Source claims about independent sets, bases, coindependence, cocircuits, and nonloops use Mathlib predicates `M.Indep`, `M.IsBase`, `M.Coindep`, `M.IsCocircuit`, and `M.IsNonloop`.
- Candidate skeletons were used only as naming and shape hints. Their `IsIndependent`/`IsCoindependent`/`IsCocircuit` predicate names and several exact-name stubs were not adopted because Mathlib uses the method-style predicates above and because `True` stubs would not cover the source.

## Required Names

- `contract`
- `contract_ground`
- `dual_contract`
- `Coindep.coindep_contract_of_disjoint`
- `contract_empty`
- `contract_eq_contract_iff`
- `coindep_contract_iff`
- `contract_isCocircuit_iff`
- `Indep.contract_isBase_iff`
- `Indep.contract_indep_iff`
- `IsNonloop.contractElem_indep_iff`
- `IsBasis.contract_eq_contract_delete`

## Source Statement Inventory

Machine-readable source inventory index:

| Source label | Kind | Source lines | Planned Lean declaration |
| --- | --- | --- | --- |
| `line-17` | definition | 17-23 | `contract` |
| `line-25` | lemma | 25-36 | `contract_ground` |
| `line-38` | lemma | 38-50 | `dual_contract` |
| `line-52` | lemma | 52-68 | `Coindep.coindep_contract_of_disjoint` |
| `line-70` | lemma | 70-80 | `contract_empty` |
| `line-82` | lemma | 82-94 | `contract_eq_contract_iff` |
| `line-96` | lemma | 96-109 | `coindep_contract_iff` |
| `line-111` | lemma | 111-120 | `contract_isCocircuit_iff` |
| `line-122` | lemma | 122-136 | `Indep.contract_isBase_iff` |
| `line-138` | lemma | 138-153 | `Indep.contract_indep_iff` |
| `line-155` | lemma | 155-170 | `IsNonloop.contractElem_indep_iff` |
| `line-172` | lemma | 172-185 | `IsBasis.contract_eq_contract_delete` |

### line-17

- Source locator: `docs/source.tex`, lines 17-23.
- Source statement: Let `M` be a matroid on a ground set `E`, and let `C ⊆ E`. The contraction of `C` from `M`, denoted `M / C`, is defined by `M / C := (M^* \setminus C)^*`.
- Planned Lean declarations: `contract`.
- Lean statement/body: `def contract {α : Type*} (M : Matroid α) (C : Set α) : Matroid α := (M✶ ＼ C)✶`.
- Skeleton candidate used: Skeletons 1-4 suggested a top-level `contract`; the final declaration keeps that name but replaces the construction `sorry` with Mathlib's dual-deletion body.
- Dependencies: `Matroid.dual`, matroid deletion notation `＼`, Mathlib contraction convention.
- Formal statement review: The Lean body is exactly the source formula with `M✶` for dual and `＼` for deletion. The source's ambient ground set `E` is represented by `M.E`; the function is total in `C` following Mathlib.
- Source qualifiers: matroid object class; ground set `E`; parameter set `C ⊆ E`; output is a matroid; equality/definition by dual deletion.
- Lean coverage: exact formula with a total-domain bridge for `C : Set α`.
- Scope changes: `C` is not packaged as a subtype carrying `C ⊆ M.E`; theorems record source subset hypotheses where explicit.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Definition only. Later proofs should unfold `contract` or rewrite to Mathlib's `Matroid.contract`; the body is definitionally `(M✶ ＼ C)✶`.

### line-25

- Source locator: `docs/source.tex`, statement lines 25-30, proof lines 30-36.
- Source statement: For any matroid `M` and set `C ⊆ E`, `E(M / C) = E(M) \setminus C`.
- Planned Lean declarations: `contract_ground`.
- Lean statement: `theorem contract_ground {α : Type*} (M : Matroid α) (C : Set α) (hC : C ⊆ M.E) : (contract M C).E = M.E \ C`.
- Skeleton candidate used: Skeletons 1-4 suggested the top-level name and ground-set equality; final statement replaces non-Mathlib `groundSet` with `E` and includes the source subset hypothesis.
- Dependencies: `contract`; Mathlib `Matroid.contract_ground`; dual and deletion ground-set facts.
- Formal statement review: `E(M / C)` is represented by `(contract M C).E`; `E(M)` by `M.E`; set difference by `\`; the explicit source condition `C ⊆ E` is `hC`.
- Source qualifiers: matroid `M`; set `C` in the ground; equality of ground sets; output codomain is a set of elements.
- Lean coverage: exact source statement with Mathlib notation.
- Scope changes: none beyond `E(M)` as `M.E`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: By definition `M / C = (M^* \setminus C)^*`. Taking ground sets and using the corresponding facts for deletion and duality yields `E(M / C) = E(M) \setminus C`.
- Source proof / prover notes: Unfold `contract`, use dual ground invariance and deletion ground-set computation; Mathlib likely closes with `simpa [contract] using Matroid.contract_ground M C`.

### line-38

- Source locator: `docs/source.tex`, statement lines 38-45, proof lines 45-50.
- Source statement: For any matroid `M` and set `X ⊆ E`, `(M / X)^* = M^* \setminus X` and `(M \setminus X)^* = M^* / X`.
- Planned Lean declarations: `dual_contract`.
- Lean statement: `theorem dual_contract {α : Type*} (M : Matroid α) (X : Set α) (hX : X ⊆ M.E) : (contract M X)✶ = M✶ ＼ X ∧ (M ＼ X)✶ = contract M✶ X`.
- Skeleton candidate used: Skeletons 1-4 suggested a conjunction; final statement corrects the second conjunct to contract the dual matroid `M✶`, matching the source `M^* / X`, and includes the source subset hypothesis.
- Dependencies: `contract`; Mathlib `Matroid.dual_contract`; Mathlib `Matroid.dual_delete`.
- Formal statement review: The first conjunct is the dual of contraction; the second is the dual of deletion. The target `contract M✶ X` represents `M^* / X`.
- Source qualifiers: matroid `M`; set `X ⊆ E`; two equality claims; duality and deletion/contraction bridge.
- Lean coverage: exact two-part source claim as a conjunction.
- Scope changes: none beyond Lean notation and total-domain wrapper.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: Both identities follow directly from the definition of contraction `M / X := (M^* \setminus X)^*` and the involutivity of matroid duality.
- Source proof / prover notes: Use `contract` plus `Matroid.dual_contract` for the first equality and `Matroid.dual_delete` for the second; dual involutivity may appear as `dual_dual`.

### line-52

- Source locator: `docs/source.tex`, statement lines 52-61, proof lines 61-68.
- Source statement: For any matroid `M` and sets `C₁, C₂ ⊆ E`, `M / C₁ / C₂ = M / (C₁ ∪ C₂)`. In particular, `M / C₁ / C₂ = M / C₂ / C₁`.
- Planned Lean declarations: `Coindep.coindep_contract_of_disjoint`.
- Lean statement: `theorem Coindep.coindep_contract_of_disjoint {α : Type*} (M : Matroid α) (C₁ C₂ : Set α) (hC₁ : C₁ ⊆ M.E) (hC₂ : C₂ ⊆ M.E) : contract (contract M C₁) C₂ = contract M (C₁ ∪ C₂) ∧ contract (contract M C₁) C₂ = contract (contract M C₂) C₁`.
- Skeleton candidate used: Skeleton4 had the exact namespace name; final statement replaces the weak one-claim skeleton by a conjunction covering both the main claim and the “in particular” claim.
- Dependencies: `contract`; Mathlib `Matroid.contract_contract`; Mathlib `Matroid.contract_comm`; union commutativity.
- Formal statement review: Iterated source notation `M / C₁ / C₂` is represented as `contract (contract M C₁) C₂`; the in-particular commuted equality is included explicitly.
- Source qualifiers: matroid `M`; sets `C₁, C₂ ⊆ E`; equality of matroids; follow-on commutativity claim.
- Lean coverage: exact source coverage including the follow-on claim.
- Scope changes: none beyond Lean notation and total-domain wrapper.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: Using the definition of contraction via duality, iterated contraction corresponds to iterated deletion in the dual matroid. Since deletion distributes over unions, the result follows. Commutativity is immediate from the commutativity of union.
- Source proof / prover notes: Use `Matroid.contract_contract` for the first conjunct and either `Matroid.contract_comm` or the first conjunct plus `union_comm` for the second.

### line-70

- Source locator: `docs/source.tex`, statement lines 70-75, proof lines 75-80.
- Source statement: For any matroid `M`, `M / ∅ = M`.
- Planned Lean declarations: `contract_empty`.
- Lean statement: `theorem contract_empty {α : Type*} (M : Matroid α) : contract M ∅ = M`.
- Skeleton candidate used: Skeletons 1-4 suggested this top-level equality; final statement uses the implemented wrapper.
- Dependencies: `contract`; Mathlib `Matroid.contract_empty`; deletion-empty and dual-involutive facts.
- Formal statement review: The Lean statement is a direct translation with `∅` as the empty set and `contract M ∅` as `M / ∅`.
- Source qualifiers: matroid `M`; empty contraction; equality of matroids.
- Lean coverage: exact.
- Scope changes: none.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: This follows from the definition of contraction and the fact that deleting the empty set has no effect on a matroid.
- Source proof / prover notes: Unfold `contract`; use deletion of `∅` and dual involutivity, or `Matroid.contract_empty`.

### line-82

- Source locator: `docs/source.tex`, statement lines 82-89, proof lines 89-94.
- Source statement: For any matroid `M` and sets `C₁, C₂ ⊆ E`, `M / C₁ = M / C₂ ↔ C₁ ∩ E(M) = C₂ ∩ E(M)`.
- Planned Lean declarations: `contract_eq_contract_iff`.
- Lean statement: `theorem contract_eq_contract_iff {α : Type*} (M : Matroid α) (C₁ C₂ : Set α) (hC₁ : C₁ ⊆ M.E) (hC₂ : C₂ ⊆ M.E) : contract M C₁ = contract M C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E`.
- Skeleton candidate used: Skeletons 1-4 suggested the top-level equivalence; final statement replaces `groundSet` with `E` and includes the source subset hypotheses.
- Dependencies: `contract`; Mathlib `Matroid.contract_eq_contract_iff`; Mathlib deletion equality criterion; dual ground facts.
- Formal statement review: `E(M)` is `M.E`, intersection is Lean set intersection, and equality of contractions is stated for the wrapper `contract`.
- Source qualifiers: matroid `M`; sets `C₁, C₂ ⊆ E`; equivalence; equality condition on intersections with the ground set.
- Lean coverage: exact source statement.
- Scope changes: none beyond Lean notation.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: Using the dual characterization of contraction, the statement reduces to the corresponding criterion for equality of deletions in the dual matroid.
- Source proof / prover notes: Rewrite `contract` to Mathlib contraction and use `Matroid.contract_eq_contract_iff`; source subset hypotheses can be unused.

### line-96

- Source locator: `docs/source.tex`, statement lines 96-104, proof lines 104-109.
- Source statement: Let `M` be a matroid, `C ⊆ E(M)`, and `X ⊆ E(M)`. Then `X` is coindependent in `M / C` iff `X` is coindependent in `M` and `X ∩ C = ∅`.
- Planned Lean declarations: `coindep_contract_iff`.
- Lean statement: `theorem coindep_contract_iff {α : Type*} (M : Matroid α) (C X : Set α) (hC : C ⊆ M.E) (hX : X ⊆ M.E) : (contract M C).Coindep X ↔ M.Coindep X ∧ X ∩ C = ∅`.
- Skeleton candidate used: Skeletons suggested the shape but used non-Mathlib `IsCoindependent`; final statement uses Mathlib's `M.Coindep X` and preserves the empty-intersection surface condition.
- Dependencies: `contract`; Mathlib `Matroid.coindep_contract_iff`; `Disjoint`/empty-intersection conversions; dual/delete independence facts.
- Formal statement review: Coindependence is represented by `Coindep`; both source subset hypotheses are explicit; the RHS is conjunction with literal empty intersection.
- Source qualifiers: matroid `M`; subsets `C` and `X` of the ground; coindependence in contracted matroid; coindependence in original matroid; disjointness/empty intersection side condition.
- Lean coverage: exact source statement.
- Scope changes: none beyond Lean notation.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: This follows by rewriting coindependence in terms of independence in the dual matroid and applying the characterization of deletion.
- Source proof / prover notes: Use `Matroid.coindep_contract_iff`, then convert `Disjoint X C` to `X ∩ C = ∅` with set extensionality or `disjoint_iff_inter_eq_empty`.

### line-111

- Source locator: `docs/source.tex`, statement lines 111-115, proof lines 115-120.
- Source statement: Let `M` be a matroid and `C ⊆ E(M)`. A set `K` is a cocircuit of `M / C` iff `K` is a cocircuit of `M` and `K ∩ C = ∅`.
- Planned Lean declarations: `contract_isCocircuit_iff`.
- Lean statement: `theorem contract_isCocircuit_iff {α : Type*} (M : Matroid α) (C K : Set α) (hC : C ⊆ M.E) : (contract M C).IsCocircuit K ↔ M.IsCocircuit K ∧ K ∩ C = ∅`.
- Skeleton candidate used: Skeletons suggested the shape but used a non-Mathlib top-level `IsCocircuit`; final statement uses `M.IsCocircuit K`.
- Dependencies: `contract`; Mathlib `Matroid.contract_isCocircuit_iff`; previous coindependence characterization; circuit/cocircuit definitions.
- Formal statement review: The source cocircuit predicate is represented by Mathlib's method predicate; the source empty-intersection condition is preserved.
- Source qualifiers: matroid `M`; subset `C` of ground; set `K`; cocircuit equivalence; disjointness side condition.
- Lean coverage: exact source statement.
- Scope changes: none beyond Lean notation.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: This is an immediate consequence of the previous lemma together with the definition of cocircuits in terms of coindependence.
- Source proof / prover notes: Use Mathlib's `Matroid.contract_isCocircuit_iff` and convert `Disjoint K C` to `K ∩ C = ∅`.

### line-122

- Source locator: `docs/source.tex`, statement lines 122-130, proof lines 130-136.
- Source statement: Let `M` be a matroid and let `I ⊆ E(M)` be independent. A set `B` is a basis of `M / I` iff `B ∪ I` is a basis of `M` and `B ∩ I = ∅`.
- Planned Lean declarations: `Indep.contract_isBase_iff`.
- Lean statement: `theorem Indep.contract_isBase_iff {α : Type*} (M : Matroid α) (I B : Set α) (hI : M.Indep I) : (contract M I).IsBase B ↔ M.IsBase (B ∪ I) ∧ B ∩ I = ∅`.
- Skeleton candidate used: Skeleton4 used the exact namespace name; final statement replaces non-Mathlib `IsBase` with method-style `M.IsBase` and keeps `hI : M.Indep I` for the source independent-set assumption.
- Dependencies: `contract`; Mathlib `Matroid.Indep.contract_isBase_iff`; dual/delete base characterization.
- Formal statement review: `hI : M.Indep I` encodes both `I ⊆ M.E` and independence. The basis of `M / I` is `(contract M I).IsBase B`.
- Source qualifiers: matroid `M`; independent set `I` in the ground; set `B`; basis equivalence; union basis condition; empty intersection condition.
- Lean coverage: exact source statement, with `M.Indep I` as the standard Lean package for “`I ⊆ E(M)` and independent”.
- Scope changes: no separate subset hypothesis for `I`; it is contained in `M.Indep I`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: Using duality, the statement reduces to the corresponding characterization of bases under deletion. Translating back yields the claim.
- Source proof / prover notes: Rewrite wrapper `contract`, use `Matroid.Indep.contract_isBase_iff`, then convert `Disjoint B I` to `B ∩ I = ∅` if needed.

### line-138

- Source locator: `docs/source.tex`, statement lines 138-148, proof lines 148-153.
- Source statement: Let `M` be a matroid and let `I ⊆ E(M)` be independent. For any set `J ⊆ E(M)`, `J` is independent in `M / I` iff `J ∩ I = ∅` and `J ∪ I` is independent in `M`.
- Planned Lean declarations: `Indep.contract_indep_iff`.
- Lean statement: `theorem Indep.contract_indep_iff {α : Type*} (M : Matroid α) (I J : Set α) (hI : M.Indep I) (hJ : J ⊆ M.E) : (contract M I).Indep J ↔ J ∩ I = ∅ ∧ M.Indep (J ∪ I)`.
- Skeleton candidate used: Skeleton4 used the exact namespace name but omitted the source `J ⊆ E(M)` condition; final statement includes it and uses Mathlib's `Indep` predicate.
- Dependencies: `contract`; `Indep.contract_isBase_iff`; Mathlib `Matroid.Indep.contract_indep_iff`; basis containment characterization.
- Formal statement review: `hI` packages the source independent-set assumption; `hJ` records the source domain for `J`; empty intersection and union order match the source.
- Source qualifiers: matroid `M`; independent set `I` in ground; set `J` in ground; independence equivalence; empty intersection; union independence.
- Lean coverage: exact source statement.
- Scope changes: no separate subset hypothesis for `I` because it is included in `hI : M.Indep I`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: A set is independent if and only if it is contained in a basis. Applying the previous lemma on bases yields the equivalence.
- Source proof / prover notes: Use `Matroid.Indep.contract_indep_iff`; convert Mathlib's `Disjoint J I` condition to `J ∩ I = ∅`. The local previous theorem can also be used after proving existence of bases.

### line-155

- Source locator: `docs/source.tex`, statement lines 155-165, proof lines 165-170.
- Source statement: Let `M` be a matroid and let `e` be a non-loop element of `M`. For any set `I`, `I` is independent in `M / {e}` iff `e ∉ I` and `I ∪ {e}` is independent in `M`.
- Planned Lean declarations: `IsNonloop.contractElem_indep_iff`.
- Lean statement: `theorem IsNonloop.contractElem_indep_iff {α : Type*} (M : Matroid α) (e : α) (I : Set α) (he : M.IsNonloop e) : (contract M {e}).Indep I ↔ e ∉ I ∧ M.Indep (I ∪ {e})`.
- Skeleton candidate used: Skeleton4 used the exact namespace name; final statement restores the source's `e ∉ I` condition, which one skeleton had dropped, and uses Mathlib's `M.IsNonloop e`.
- Dependencies: `contract`; `Indep.contract_indep_iff`; Mathlib `Matroid.IsNonloop.contractElem_indep_iff`; singleton/set-insert conversions.
- Formal statement review: Non-loop is represented by `M.IsNonloop e`; singleton contraction is `contract M {e}`; the RHS keeps the source union with `{e}`.
- Source qualifiers: matroid `M`; element `e`; non-loop side condition; arbitrary set `I`; independence equivalence; membership exclusion; singleton union independence.
- Lean coverage: exact source statement.
- Scope changes: Mathlib often states the union as `insert e I`; Lean statement keeps `I ∪ {e}` for source fidelity.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: This is the specialization of the previous lemma to the case `I = {e}`, using that `e` is independent.
- Source proof / prover notes: Use `he.indep` and `Matroid.IsNonloop.contractElem_indep_iff`, then convert `insert e I` and `I ∪ {e}` with set extensionality/simp.

### line-172

- Source locator: `docs/source.tex`, statement lines 172-178, proof lines 178-185.
- Source statement: Let `M` be a matroid, `X ⊆ E(M)`, and let `I` be a basis of `X`. Then `M / X = M / I \setminus (X \setminus I)`.
- Planned Lean declarations: `IsBasis.contract_eq_contract_delete`.
- Lean statement: `theorem IsBasis.contract_eq_contract_delete {α : Type*} (M : Matroid α) (X I : Set α) (hX : X ⊆ M.E) (hI : M.IsBasis I X) : contract M X = (contract M I) ＼ (X \ I)`.
- Skeleton candidate used: Skeleton4 had the exact namespace name but a wrong implication-shaped statement; final statement matches the source equality and uses Mathlib's `M.IsBasis I X`.
- Dependencies: `contract`; Mathlib `Matroid.IsBasis.contract_eq_contract_delete`; contraction/deletion commutation; basis closure facts.
- Formal statement review: The basis-of-a-set assumption is `M.IsBasis I X`; the right side is contraction by `I` followed by matroid deletion of the set difference `X \ I`.
- Source qualifiers: matroid `M`; subset `X` of ground; set `I`; basis-of-`X` side condition; equality of matroids; contraction followed by deletion.
- Lean coverage: exact source statement.
- Scope changes: `hI : M.IsBasis I X` carries the usual Lean basis data; `hX` records the source domain for `X` explicitly.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: Decompose `X` as the disjoint union of the basis `I` and the remaining elements `X \setminus I`. Contracting `X` is equivalent to contracting `I` and deleting the remaining elements, which gives the stated equality.
- Source proof / prover notes: Use `Matroid.IsBasis.contract_eq_contract_delete`; rewrite the wrapper `contract` on both sides. Set difference is Lean `X \ I` and deletion is matroid `＼`.

## Handoff Checklist

- [x] Source document `docs/source.tex` inspected and all theorem-like blocks inventoried.
- [x] Companion instructions and all four candidate skeletons read and compared against the source.
- [x] Mathlib/local search performed before drafting; relevant existing contraction declarations recorded above.
- [x] `contract` is implemented as a real definition, not a construction stub.
- [x] Each source lemma/theorem has a drafted Lean declaration and a compact source-aware doc comment in `Main.lean`.
- [x] `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.

Suggested next command after independent statement/source review: `/prove ShadowBench/Source/Main.lean`.
