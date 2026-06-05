# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the single source-backed theorem declaration for source entry `line-17`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so a project build reaches the generated target module.

## Import Plan

Direct Lean imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
```

## Suggested Search Modules

These are proof-search references only, not current direct imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`: contains the corresponding Mathlib proof and the same fpqc descent statement as an instance.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`: used near the Mathlib fpqc isomorphism-descent proof.

## Required Names

- `AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem lines 17-19; proof lines 19-30.
- Source statement: "Being an open immersion satisfies fpqc descent."
- Planned Lean declarations: `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`.
- Lean declaration kind: `theorem` proving the proposition `IsOpenImmersion.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` inside namespace `AlgebraicGeometry`.
- Skeleton candidate used: the provided skeletons supplied the required name only. Their explicit biconditional over an `IsFpqcCovering` predicate and `BaseChange.mk` was rejected because the source is a morphism-property descent theorem and Mathlib represents fpqc descent as `DescendsAlong` along `Surjective ⊓ Flat ⊓ QuasiCompact`.
- Dependencies: `MorphismProperty.DescendsAlong`, `AlgebraicGeometry.IsOpenImmersion`, `AlgebraicGeometry.Surjective`, `AlgebraicGeometry.Flat`, `AlgebraicGeometry.QuasiCompact`, pullback stability of open immersions, descent of universal openness and universal injectivity, fpqc descent for isomorphisms, and faithfully flat ring-hom descent.
- Formal statement review: The Lean type states exactly that the morphism property `IsOpenImmersion` descends along the fpqc morphism property `@Surjective ⊓ @Flat ⊓ @QuasiCompact`. This matches the source sentence “Being an open immersion satisfies fpqc descent” at the standard Mathlib morphism-property level. The source proof begins with affine flat surjective covers and then concludes arbitrary flat surjective descent; the theorem name and fpqc convention supply the quasi-compact component in Lean. The declaration is a theorem rather than an instance so the managed prover queue has a named theorem target, but the proposition is the same as Mathlib's instance statement.
- Source qualifiers:
  - Mathematical object class: morphisms of schemes.
  - Quantification: arbitrary source, target, and base-change morphisms are covered through `MorphismProperty.DescendsAlong`.
  - Parameter domain: fpqc descent morphisms, represented by the property `@Surjective ⊓ @Flat ⊓ @QuasiCompact`.
  - Output codomain: the descended morphism satisfies `IsOpenImmersion`.
  - Side conditions: the hypothesis that the pullback/base change has `IsOpenImmersion` and that the cover has the fpqc property are packaged by `DescendsAlong`.
  - Follow-on proof content: openness and universal injectivity descend first; the proof then reduces over affine opens to descent of isomorphisms and uses faithful flat descent on coordinate rings.
- Lean coverage: The proposition `IsOpenImmersion.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` covers all source qualifiers: scheme morphisms are the ambient category, the fpqc cover condition is the intersection of surjectivity, flatness, and quasi-compactness, the base-change implication is the content of `DescendsAlong`, and the descended property is `IsOpenImmersion`.
- Scope changes: The only representation change is using Mathlib's `MorphismProperty.DescendsAlong` package instead of spelling out each base-change morphism in an elementwise theorem. This is the intended formal bridge for “satisfies fpqc descent” and does not change the mathematical claim. The Lean draft is a named theorem rather than an instance to keep the declaration in the theorem queue; its proposition matches the instance-level statement.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: The complete source proof says: Let S' → S be a flat surjective morphism of affine schemes and f : X → S a morphism. If the base change f' : X' → S' is an open immersion, then f' is universally open and universally injective, so f is universally open and universally injective; hence f(X) is open. It suffices to show for every affine open U in f(X) that f⁻¹(U) → U is an isomorphism. After pulling U back to U' in S', the map U' → U is faithfully flat between affines and the pulled-back morphism is an isomorphism. Thus reduce to the case where the base change is an isomorphism. In that case f is surjective, universally injective, and universally open, hence a homeomorphism and affine; the isomorphism O(S') → O(X') = O(S') ⊗_{O(S)} O(X), together with faithful flatness of O(S) → O(S'), implies O(S) → O(X) is an isomorphism, so f is an isomorphism. Prover strategy: follow the Mathlib proof in `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`; use `DescendsAlong.mk'`, `MorphismProperty.of_pullback_fst_of_descendsAlong` for `UniversallyOpen`, construct the open range `U : Z.Opens`, define `g' : Y ⟶ U` via `IsOpenImmersion.lift`, prove the relevant pullback map is an isomorphism using `isIso_iff_isOpenImmersion_and_surjective`, invoke fpqc descent for `isomorphisms Scheme`, and compose back with the open immersion of the image.

## Formalization Rules Recorded from `docs/instructions.md`

```text
open CategoryTheory Limits MorphismProperty

Formalize in Lean the Theorem (descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact') from Text.
The theorem must be named `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`.
```

## Handoff Checklist

- [ ] Run independent statement/source verification review and apply corrections.
- [ ] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.

## Handoff Notes

- The theorem proof is intentionally left as `by sorry` for the managed prover workflow after statement/source review.
- Source statement approved by formalization PASS and 2026-06-05 audit after checking source qualifiers, Lean coverage, and doc-comment proof notes.
- Suggested next command after review: `/prove ShadowBench/Source/Main.lean AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`.
