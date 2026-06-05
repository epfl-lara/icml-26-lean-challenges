# Formalization Blueprint: `topology/L2/top_gen_L2_016`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file formalization for all source entries.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level `lake build` covers the generated target module.

No split into auxiliary files is currently needed because the source contains one construction and two short source-backed theorem entries, all represented by Mathlib's alternating face map complex API.

## Import Plan

Direct Lean imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
```

This direct import provides the Mathlib construction `AlgebraicTopology.alternatingFaceMapComplex`, the normalized Moore complex, and `AlgebraicTopology.inclusionOfMooreComplex`. It also exports the lower-level imports suggested in `docs/instructions.md` (`MooreComplex`, `BigOperators.Fin`, and `Idempotents.FunctorCategories`), so the target file only needs this one direct import.

## Suggested Search Modules

These are non-gating proof-search hints, not target-file imports unless a prover later verifies that a direct import is needed:

- `Mathlib.AlgebraicTopology.AlternatingFaceMapComplex`
- `Mathlib.AlgebraicTopology.DoldKan.Normalized` for optional global mono/split-mono facts about `inclusionOfMooreComplexMap`

## Required Names

- `alternatingFaceMapComplex`
- `map_f`
- `inclusionOfMooreComplex`

## Candidate Skeleton Review

- `Skeleton1.lean` and `Skeleton2.lean` give the required names but use construction stubs, an imprecise `ChainComplex.{0} C` target, and a guessed `NormalizedMooreComplex` name. They are not source-faithful enough to copy.
- `Skeleton3.lean` adds the missing exact-name `map_f` stub but keeps construction stubs and theorem statements that are too weak.
- `Skeleton4.lean` contains a malformed duplicate `:= by sorry` and is not usable as Lean.
- Final draft choice: use only the skeleton-provided required names and the instruction-provided open/import hints. The actual statements are based on `docs/source.tex` and Mathlib search results for `AlgebraicTopology.alternatingFaceMapComplex`, `AlgebraicTopology.AlternatingFaceMapComplex.map_f`, and `AlgebraicTopology.inclusionOfMooreComplex`.

## Source Inventory Summary

- `line-17`: source definition `alternatingFaceMapComplex`; planned Lean declaration `alternatingFaceMapComplex`.
- `line-29`: source theorem `map_f`; planned Lean declaration `map_f`.
- `line-44`: source theorem `inclusionOfMooreComplex`; planned Lean declaration `inclusionOfMooreComplex`.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Entry title: `alternatingFaceMapComplex`
- Kind: definition.
- Planned Lean declarations: `alternatingFaceMapComplex`.
- Lean declaration shape: implemented as a Lean definition with type `SimplicialObject C ⥤ ChainComplex C ℕ`.
- Source locator: `docs/source.tex`, lines 17--27.
- Skeleton candidate used: skeletons supplied only the required Lean name; the final declaration is the Mathlib-backed construction.
- Dependencies: `CategoryTheory.Category`, `CategoryTheory.Preadditive`, `SimplicialObject`, `ChainComplex`, `AlgebraicTopology.alternatingFaceMapComplex`.
- Source statement: Let `C` be a preadditive category. Define the alternating face map complex functor `C_• : sC → Ch_{≥0}(C)`, with `C_n(X) = X_n`, differential an alternating sum of face maps, and morphism action `C_n(f) = f_n`.
- Source qualifiers:
  - mathematical object class and side conditions: a type `C` with a category structure and a preadditive structure;
  - quantifier order / parameter domain: for each such `C`, define one functor on the category of simplicial objects in `C`;
  - output codomain: nonnegatively indexed chain complexes in `C`;
  - object-action equality condition: for every simplicial object `X` and every `n ≥ 0`, the degree `n` object is `X_n`;
  - differential equality condition: the differential from degree `n + 1` to `n` is the alternating sum of face maps from `X_{n+1}` to `X_n`;
  - morphism-action equality condition: for every simplicial morphism `f : X ⟶ Y` and every `n`, the degree `n` component is the simplicial component `f_n`;
  - follow-on claim: no separate theorem is stated in this definition; well-definedness is the next source theorem `line-29`.
- Lean coverage: implemented as the top-level `def alternatingFaceMapComplex`, with value `AlgebraicTopology.alternatingFaceMapComplex C`, whose type is `SimplicialObject C ⥤ ChainComplex C ℕ`. Its type covers the source domain/codomain, and Mathlib API lemmas `AlgebraicTopology.alternatingFaceMapComplex_obj_X`, `AlgebraicTopology.alternatingFaceMapComplex_obj_d`, `AlgebraicTopology.AlternatingFaceMapComplex.objD`, and `AlgebraicTopology.alternatingFaceMapComplex_map_f` cover the source object, differential, and morphism formulas.
- Scope changes:
  - The source display says `(-1)^n d_i^n`; the source proof uses signs `(-1)^{i+j}` and the standard alternating face map complex uses `(-1)^i`. The Lean draft follows the intended standard Mathlib construction with sign `(-1)^i` and records this source typo/ambiguity explicitly.
  - The source notation `Ch_{≥0}(C)` is represented by `ChainComplex C ℕ`.
- Formal statement review: source claim is a construction, so the Lean declaration is an implemented `def`, not a theorem or a construction stub; no source-fidelity blocker was found.
- Lean doc-comment proof notes: definition doc comment records the source locator and sign ambiguity.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no separate proof appears inside the source definition. Later theorem `map_f` carries the well-definedness proof notes.

### line-29

- Source inventory entry: `line-29`
- Kind: theorem.
- Planned Lean declarations: `map_f`. Theorem over a preadditive category, recording object components, the alternating differential formula, the consecutive-differential square-zero condition, and morphism components.
- Source locator: `docs/source.tex`, theorem lines 29--31 and proof lines 31--42.
- Skeleton candidate used: skeletons supplied only the exact Lean name; weak `True` stubs were rejected.
- Dependencies: `alternatingFaceMapComplex`, `AlgebraicTopology.alternatingFaceMapComplex_obj_X`, `AlgebraicTopology.alternatingFaceMapComplex_obj_d`, `AlgebraicTopology.AlternatingFaceMapComplex.objD`, `AlgebraicTopology.AlternatingFaceMapComplex.d_squared`, `AlgebraicTopology.alternatingFaceMapComplex_map_f`.
- Source statement: The functor `C_•` is a well-defined functor.
- Complete source proof text: "We first show that it is well-defined on objects. That is, for each simplicial object `X` of `C`, the sequence `C_•(X)` together with `d_•` is a chain complex. It suffices to show that `d_{n-1} ∘ d_n = 0` for all `n=1,2,...`, and we have `d_{n-1} ∘ d_n = Σ_{i=0}^{n-1} Σ_{j=0}^n (-1)^{i+j} d_i^{n-1} ∘ d_j^n = Σ_{i < j} (-1)^{i+j} d_i^{n-1} ∘ d_j^n + Σ_{i ≥ j} (-1)^{i+j} d_i^{n-1} ∘ d_j^n = Σ_{i < j} (-1)^{i+j} d_{j-1}^{n-1} ∘ d_i^n + Σ_{i ≥ j} (-1)^{i+j} d_i^{n-1} ∘ d_j^n = Σ_{i ≤ j'} (-1)^{i+j'+1} d_{j'}^{n-1} ∘ d_i^n + Σ_{i ≥ j} (-1)^{i+j} d_i^{n-1} ∘ d_j^n = 0`. For a morphism `f : X → Y`, `f_n`'s commute with the face maps of `X` and `Y`, and hence `f` is compatible with the differentials of `C_•(X)` and `C_•(Y)`. That is, `f_{n-1} ∘ d_n = d_n ∘ f_n` for each `n`, and thus `C_•(f)` is a well-defined morphism from `C_•(X)` to `C_•(Y)`."
- Source qualifiers:
  - mathematical object class and side conditions: a preadditive category `C`;
  - quantifier order / parameter domain: after the construction of `C_•`, for every simplicial object `X` and every positive differential degree, the constructed object data form a chain complex; for every simplicial morphism `f : X ⟶ Y`, the constructed degreewise maps form a morphism of chain complexes;
  - output codomain: a functor `SimplicialObject C ⥤ ChainComplex C ℕ`;
  - equality conditions: `C_n(X) = X_n`, the differential is the alternating face-map sum, and `C_n(f) = f_n`;
  - chain-complex side condition: consecutive differentials compose to zero;
  - morphism side condition: the degreewise maps commute with the alternating differentials, hence define chain maps;
  - follow-on claim: functoriality is part of the Lean `Functor` type of `alternatingFaceMapComplex C`.
- Lean coverage: the corrected Lean theorem `map_f` asserts four source-facing facts: object component equality, the explicit alternating differential sum formula, `AlgebraicTopology.AlternatingFaceMapComplex.objD X (n + 1) ≫ ... objD X n = 0`, and the morphism component formula. The statement is over `[Category C] [Preadditive C]`, matching the source object class. The fact that these data assemble into a functor is represented by the type of `alternatingFaceMapComplex C : SimplicialObject C ⥤ ChainComplex C ℕ`.
- Scope changes:
  - Lean does not have a separate predicate for "is a well-defined functor" once a term has type `SimplicialObject C ⥤ ChainComplex C ℕ`; this source phrase is represented by the functor type together with the theorem's source-facing component, differential, square-zero, and morphism formulas.
  - The differential sign follows the standard `(-1)^i` convention, as in Mathlib and the source proof's cancellation signs; this is the same source typo/ambiguity recorded in `line-17`.
- Formal statement review: no source-fidelity blocker was found after strengthening the Lean statement from a bare alias equality to source-facing formulas.
- Lean doc-comment proof notes: doc comment above `map_f` contains the source proof sketch and exact Mathlib theorem names for the prover.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Prover notes: prove by unfolding `alternatingFaceMapComplex`; the object and morphism formulas follow from `AlgebraicTopology.alternatingFaceMapComplex_obj_X` and `AlgebraicTopology.alternatingFaceMapComplex_map_f`, the differential formula from `AlgebraicTopology.alternatingFaceMapComplex_obj_d` plus `AlgebraicTopology.AlternatingFaceMapComplex.objD`, and the square-zero conjunct from `AlgebraicTopology.AlternatingFaceMapComplex.d_squared`.

### line-44

- Source inventory entry: `line-44`
- Entry title: `inclusionOfMooreComplex`
- Kind: theorem.
- Planned Lean declarations: `inclusionOfMooreComplex`. Existential theorem over an abelian category, with a natural-transformation witness, degreewise mono/inclusion condition, and the levelwise subobject-arrow formula.
- Source locator: `docs/source.tex`, theorem lines 44--46 and proof lines 46--59.
- Skeleton candidate used: skeletons supplied only the required name; guessed `NormalizedMooreComplex` functor notation and weak `true` conclusions were rejected.
- Dependencies: `AlgebraicTopology.normalizedMooreComplex`, `alternatingFaceMapComplex`, `AlgebraicTopology.inclusionOfMooreComplex`, `AlgebraicTopology.inclusionOfMooreComplexMap_f`, `AlgebraicTopology.NormalizedMooreComplex.objX`.
- Source statement: For an abelian category `C`, there is an inclusion `N_• ↪ C_•` from the normalized Moore complex into the alternating face map complex, as a natural transformation of functors.
- Complete source proof text: "We define the map of functors `i : N_• → C_•` as follows. For a simplicial object `X` in `C` and for each `n=0,1,2,...`, we have a natural inclusion `i_n : N_n(X) = ⋃_{i=0}^n ker(d_i^n : X_n → X_{n-1}) ↪ X_n = C_n(X)`. To show that they induce an inclusion of chain complexes, it suffices to show that the inclusions above commute with the differentials. Indeed, denote the differentials of `N_•(X)`, `C_•(X)` by `d_•^N`, `d_•^C`, respectively. Then we have `d_n^C ∘ i_n = i_n ∘ Σ_{i=0}^n d_i^n|_{N_n(X)} = i_n ∘ d_0^n|_{N_n(X)} = i_n ∘ d_n^N` since `N_n(X) ⊆ ker d_i^n` for all `i=1,2,...,n`. Therefore, we have an inclusion of chain complexes `i_X : N_•(X) ↪ C_•(X)` with `(i_X)_n := i_n : N_n(X) ↪ C_n(X)`. Moreover, this inclusion defines a natural transformation since for any other simplicial object `Y` in `C` and a morphism `f : X → Y` of simplicial objects, we have `i_Y ∘ N_•(f) = C_•(f) ∘ i_X` by construction."
- Source qualifiers:
  - mathematical object class and side conditions: an abelian category `A`, hence in particular a preadditive category with kernels/intersections available;
  - quantifier order / parameter domain: for each such `A`, construct one natural transformation of functors on `SimplicialObject A`;
  - source functor: normalized Moore complex `N_•`, represented by `AlgebraicTopology.normalizedMooreComplex A`;
  - target functor / output codomain: alternating face map complex `C_•`, represented by `alternatingFaceMapComplex A`, and a natural transformation between the two functors into `ChainComplex A ℕ`;
  - inclusion condition: for each simplicial object `X` and degree `n`, the component map is an inclusion/mono into the degree `n` object of the alternating face map complex;
  - representation bridge: `N_n(X)` is the standard normalized Moore subobject, i.e. the intersection of higher face kernels, represented by `AlgebraicTopology.NormalizedMooreComplex.objX X n`;
  - differential compatibility: the component maps are morphisms of chain complexes because higher face terms vanish on the normalized Moore object and the remaining term is induced by `d_0`;
  - naturality: for simplicial morphisms `f : X ⟶ Y`, the square `i_Y ∘ N_•(f) = C_•(f) ∘ i_X` commutes as part of the natural-transformation structure.
- Lean coverage: the Lean theorem asserts existence of `η : AlgebraicTopology.normalizedMooreComplex A ⟶ alternatingFaceMapComplex A`, so the source and target functors and naturality are in the type. It additionally asserts that each degree component `(η.app X).f n` is `Mono`, and that it equals the subobject arrow `(AlgebraicTopology.NormalizedMooreComplex.objX X n).arrow`. The witness is identified with `AlgebraicTopology.inclusionOfMooreComplex A`, Mathlib's construction whose application is a chain-map inclusion, so differential compatibility is covered by the chain-map type.
- Scope changes:
  - The source display uses `⋃_{i=0}^n ker d_i^n`, but the name "normalized Moore complex", Mathlib, and the proof sentence `N_n(X) ⊆ ker d_i^n` for `i = 1, ..., n` identify the standard intersection of higher face kernels. Lean follows that standard representation through `NormalizedMooreComplex.objX` and records the display as a source typo/ambiguity.
  - The source notation `Ch_{≥0}(A)` is represented by `ChainComplex A ℕ`.
  - The theorem asserts degreewise monomorphism/inclusion. It does not separately assert a global `Mono η` instance for the natural transformation category; the source statement only requires the displayed degreewise inclusion, and optional global mono/split-mono facts are proof-search hints under `Mathlib.AlgebraicTopology.DoldKan.Normalized`.
- Formal statement review: no source-fidelity blocker was found after strengthening the Lean statement with degreewise `Mono` components.
- Lean doc-comment proof notes: doc comment above `inclusionOfMooreComplex` contains the source proof sketch, source ambiguity, and Mathlib witness/component theorem names.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Prover notes: after review, use witness `AlgebraicTopology.inclusionOfMooreComplex A`; prove the component formula with `AlgebraicTopology.inclusionOfMooreComplexMap_f` after unfolding the alias `alternatingFaceMapComplex`, and derive degreewise `Mono` from the subobject arrow formula.

## Planned Proof Queue After Review

Definitions/abbreviations implemented directly:

- `alternatingFaceMapComplex`

Theorem proof obligations intended for the later prover queue, if the independent statement/source review keeps the statements:

- `map_f`
- `inclusionOfMooreComplex`

Suggested command after statement/source review:

```text
/prove ShadowBench/Source/Main.lean
```
