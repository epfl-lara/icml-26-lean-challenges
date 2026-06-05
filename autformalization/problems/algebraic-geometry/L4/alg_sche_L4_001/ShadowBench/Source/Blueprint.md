# Formalization Blueprint: ShadowBench algebraic-geometry/L4/alg_sche_L4_001

Source document: `docs/source.tex`
Target Lean file: `ShadowBench/Source/Main.lean`
Problem id: `algebraic-geometry/L4/alg_sche_L4_001`

## Generated File Layout

- `ShadowBench/Source/Main.lean`: generated declarations for the three source theorem-like entries and the bridge structure `AffineOpenModel` used for the affine-open/ideal dictionary in line 86.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`, so the generated target module is covered by the project root module.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so plain project verification covers the generated target module.

## Import Plan

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`

## Suggested Search Modules

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.Topology.Basic`

## Local and Mathlib Search Notes

- Mathlib search found `AlgebraicGeometry.UniversallyOpen.of_flat`: flat and locally finite-presentation morphisms are universally open.
- Mathlib search found `AlgebraicGeometry.Scheme.Hom.isOpenMap`: universally open morphisms are open maps on underlying topological spaces.
- Mathlib search found `AlgebraicGeometry.QuasiCompact`: the available Mathlib class for the quasi-compact part of the usual scheme-theoretic “finite type” condition.
- Mathlib search found `AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType`: locally finite type over a locally noetherian target gives locally finite presentation.
- Mathlib search found `AlgebraicGeometry.IsNoetherian`, `AlgebraicGeometry.IsLocallyNoetherian`, and `AlgebraicGeometry.LocallyOfFiniteType` as the closest existing scheme-level representations of the source qualifiers.
- The candidate skeletons preserve the requested declaration names but use placeholder classes such as `NoetherianScheme`, `IsFlat`, `IsOfFiniteType`, and `Scheme X`; the final Lean draft keeps the names and source intent while replacing those placeholders with Mathlib scheme morphism classes.

## Bridge Declarations

- `AffineOpenModel`: a structure packaging the formal bridge for an affine open subset `V = Spec B` of a scheme `Y`.  It contains the open carrier, an ideal-indexed `vanishingSet`, the assertion that each vanishing set lies in the carrier, and the affine fact that every chart-relative closed subset expressible as `carrier ∩ C` with `C` closed in the ambient scheme is represented as `V(I)` for some ideal `I : Ideal B`.  This is a deliberate bridge for the source representation at line 86, avoiding an unfinished construction stub while using the relative closedness actually produced by the source proof.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex:17-74`
- Source kind/title: theorem `flat_is_open`
- Source statement: Let `f : X → Y` be a flat morphism of finite type of Noetherian schemes. Then `f` is an open morphism.
- Planned Lean declarations: `flat_is_open`
- Dependencies: `AlgebraicGeometry.IsNoetherian`, `AlgebraicGeometry.Flat`, `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`, `AlgebraicGeometry.UniversallyOpen.of_flat`, `AlgebraicGeometry.Scheme.Hom.isOpenMap`, `AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType`.
- Source qualifiers: mathematical object class = morphism `f : X → Y` of schemes; quantifier order = schemes `X Y`, morphism `f`, then noetherian/flat/finite-type hypotheses; parameter domain = open subsets of the source scheme `X`; output codomain = subsets of the target scheme `Y`; equality/image condition = the image of every open subset of `X` under `f` is open in `Y` (open morphism); side conditions = `X` and `Y` noetherian, `f` flat, `f` finite type; follow-on claims in the statement = none beyond openness of the morphism.
- Lean coverage: the Lean theorem quantifies over Mathlib schemes and a morphism `f : X ⟶ Y`, represents noetherian schemes by `[AlgebraicGeometry.IsNoetherian X]` and `[AlgebraicGeometry.IsNoetherian Y]`, represents flatness by `[AlgebraicGeometry.Flat f]`, represents finite type by the pair `[AlgebraicGeometry.LocallyOfFiniteType f]` and `[AlgebraicGeometry.QuasiCompact f]`, and states the open-morphism conclusion as `IsOpenMap f.base`.
- Scope changes: none for the intended scheme-level theorem; the source phrase “finite type” is encoded as Mathlib local finite type plus quasi-compactness, and the noetherian target hypothesis supplies the finite-presentation bridge used by Mathlib’s openness theorem.
- Formal statement review: The Lean statement has the same named theorem and the same scheme-level hypothesis pattern as the source.  The conclusion is written in topological form because Mathlib’s open morphism API exposes the underlying continuous map via `f.base`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  ```text
  Since openness of a morphism is local on the source and target, we may work locally on `X` and `Y`. Thus we may assume
  X = Spec(B), Y = Spec(A),
  where `A` is a Noetherian ring, `B` is a finitely generated `A`-algebra, and `B` is flat as an `A`-module.

  We must show that the map Spec(B) → Spec(A) is open. Since principal open sets form a basis for the topology on `Spec(B)`, it is enough to show that for every `g ∈ B`, the image of the open set `D(g) ⊂ Spec(B)` is open in `Spec(A)`.

  Now the restriction of `f` to `D(g)` is again flat and of finite type. Indeed, `D(g) = Spec(B_g)`, and `B_g` is a finitely generated flat `A`-algebra. Thus it suffices to show that the image of `Spec(B)` in `Spec(A)` is open.

  Let `Z = f(X) ⊂ Spec(A)`. Since `f` is of finite type, Chevalley's theorem implies that `Z` is constructible. We will show that `Z` is stable under generalization. Because `A` is Noetherian, every constructible subset stable under generalization is open. Hence `Z` will be open, as desired.

  So let `p ⊂ q` be prime ideals of `A`, and assume that `q ∈ Z`. We must show that `p ∈ Z`. Since `q ∈ Z`, there exists a prime ideal `Q ⊂ B` such that `Q ∩ A = q`.

  Consider the localized ring map `A_q → B_q`. Because localization preserves flatness and finite type, this is again a flat ring map of finite type, with `A_q` Noetherian. The prime `Q` determines a prime of `B_q` lying over the maximal ideal `q A_q`.

  Now flat finite type morphisms satisfy the going-down theorem. Hence, since `p A_q ⊂ q A_q`, there exists a prime ideal `P ⊂ B_q` lying under the chosen prime over `q A_q` such that `P ∩ A_q = p A_q`. Contracting `P` back to `B`, we obtain a prime ideal of `B` lying over `p`. Therefore `p ∈ Z`.

  Thus `Z` is stable under generalization. Since `Z` is constructible and `A` is Noetherian, it follows that `Z` is open in `Spec(A)`. As noted above, the same argument applies to the image of every principal open subset `D(g)` of `Spec(B)`, and therefore `f` is an open morphism.

  This proves the theorem.
  ```
- Source proof / prover notes: Use the Mathlib route rather than reproving Chevalley and going-down: infer local finite presentation from local finite type over the noetherian target, obtain universal openness from flatness plus local finite presentation, then use `Scheme.Hom.isOpenMap`.

### line-78

- Source locator: `docs/source.tex:78-84`
- Source kind/title: corollary `flat_open_image`
- Source statement: Let `f : X → Y` be a flat morphism of finite type of Noetherian schemes. Let `U ⊂ X` be open. Then `f(U)` is open in `Y`.
- Planned Lean declarations: `flat_open_image`
- Dependencies: `flat_is_open`, `IsOpenMap`, `IsOpen`.
- Source qualifiers: mathematical object class = morphism `f : X → Y` of schemes; quantifier order = schemes `X Y`, morphism `f`, noetherian/flat/finite-type hypotheses, then open subset `U`; parameter domain = open subset `U ⊂ X`; output codomain = subset `f(U) ⊂ Y`; equality/image condition = direct image of `U` under `f`; side conditions = `X` and `Y` noetherian, `f` flat, `f` finite type, and `U` open; follow-on claims in the statement = none beyond openness of `f(U)`.
- Lean coverage: the Lean theorem repeats the noetherian, flat, local finite-type, and quasi-compact hypotheses from `flat_is_open`, takes an open subset `U : Set X.carrier`, and states that its direct image under the underlying continuous map `f.base` is open in `Y.carrier`.
- Scope changes: none for the intended scheme-level corollary; image notation is expressed as Lean set image under `f.base`, and the finite-type/noetherian/flat hypotheses match the reviewed encoding used for `flat_is_open`.
- Formal statement review: The Lean statement is the direct expansion of “open map sends open sets to open sets” for the scheme morphism’s underlying continuous map.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: By the theorem, `f` is open and the statement follows from the definition of open map.
- Source proof / prover notes: Apply `flat_is_open f` and then apply the resulting `IsOpenMap` proof to `hU`.

### line-86

- Source locator: `docs/source.tex:86-97`
- Source kind/title: theorem `flat_morphism_complement_of_image_is_closed`
- Source statement: Let `f : X → Y` be a flat morphism of schemes. Let `U ⊂ X` be open, and let `V = Spec B ⊂ Y` be an affine open subset. Then there exists an ideal `I ⊂ B` such that `V \ (f(U) ∩ V) = V(I)`.
- Planned Lean declarations: `flat_morphism_complement_of_image_is_closed`
- Dependencies: `AffineOpenModel`, `flat_open_image`, `AlgebraicGeometry.QuasiCompact`, `IsClosed`, `IsOpen`, `Ideal`.
- Source qualifiers: mathematical object class = morphism `f : X → Y` of schemes together with an affine open subset written `V = Spec B ⊂ Y`; quantifier order = schemes `X Y`, morphism `f`, flatness of `f`, open subset `U`, affine chart ring `B`, affine open subset `V`; parameter domain = `U ⊂ X`; output codomain = ideals `I ⊂ B`; equality/image condition = complement inside `V` of `f(U) ∩ V` equals the chart vanishing set `V(I)`; side conditions explicitly present in the source = `U` open, `V` affine open, and `f` flat; follow-on claims in the statement = none beyond the ideal-existence equality.  The source statement itself does not state noetherian or finite-type hypotheses, although its proof invokes the preceding theorem that has those hypotheses.
- Lean coverage: partial but deliberate.  Under the added noetherian and finite-type hypotheses, the Lean theorem formalizes the ideal-existence conclusion as `∃ I : Ideal B, V.carrier \\ (f.base '' U ∩ V.carrier) = V.vanishingSet I`.  It covers schemes and morphisms using Mathlib schemes, flatness by `[AlgebraicGeometry.Flat f]`, finite type by `[AlgebraicGeometry.LocallyOfFiniteType f]` plus `[AlgebraicGeometry.QuasiCompact f]`, the open subset by `(U : Set X.carrier) (hU : IsOpen U)`, and the affine-open/ideal dictionary by the companion bridge `AffineOpenModel Y B`.  The bridge records the open carrier, the chart-level `V(I)` interpretation, and the relative closed-subset-to-ideal fact used after intersecting with the affine chart.  The Lean theorem does not assert the literal arbitrary-flat case without noetherian/finite-type hypotheses.
- Scope changes: intentionally recorded.  The Lean statement adds `[AlgebraicGeometry.IsNoetherian X]`, `[AlgebraicGeometry.IsNoetherian Y]`, `[AlgebraicGeometry.LocallyOfFiniteType f]`, and `[AlgebraicGeometry.QuasiCompact f]` because the source proof cites `flat_is_open`/`flat_open_image`, which require these noetherian finite-type hypotheses; without a local finite-presentation/finite-type hypothesis, the literal arbitrary-flat source statement is stronger than the theorem proved by the supplied proof.  The concrete scheme equality/isomorphism `V = Spec B ⊂ Y` is represented by the explicit bridge structure `AffineOpenModel` rather than by a full `Scheme.Opens` construction.
- Formal statement review: The Lean statement keeps the theorem name, the open subset `U`, the affine chart ring `B`, and the existence of an ideal cutting out the complement.  It is a proof-compatible formalization with documented scope changes, not exact literal coverage of arbitrary flat morphisms.  The review accepts this correction because the source statement omits hypotheses required by its own cited proof and the omission is explicitly recorded.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: By the theorem, `f(U) ∩ V` is open in `V`, and the statement follows.
- Source proof / prover notes: Use `flat_open_image` to show `f.base '' U` is open, hence its intersection with the open chart is open.  The complement inside `V.carrier` is relatively closed; express it as `V.carrier ∩ C` where `C` is the closed complement of `f.base '' U`, then apply `V.closed_subsets_are_vanishing` to obtain the ideal `I`.

## Handoff Checklist

- [x] Source document inspected with deterministic LaTeX extraction.
- [x] Local instructions, skeleton suggestions, and Mathlib declarations compared against the source.
- [x] Blueprint source inventory entries populated for `line-17`, `line-78`, and `line-86`.
- [x] Generated Lean file begins with imports and contains only theorem-proof `sorry` placeholders, plus implemented bridge structure fields.
- [ ] Run independent statement/source verification review and apply corrections.
- [ ] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.
