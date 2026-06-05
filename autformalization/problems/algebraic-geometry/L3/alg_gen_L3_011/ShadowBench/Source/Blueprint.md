# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_011`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Inventory

### `line-17` (theorem, lines 17-18) — `isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal`

- Source inventory entry: line-17.
- Preflight label: `line-17`.
- Kind: theorem.
- Source name: `isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal`.
- Source locator: `docs/source.tex`, theorem lines 17-18; proof environment lines 19-21 (proof text line 20).
- Source statement: Let `g : X → Y` be a morphism of schemes over `S`. If `X` is affine over `S` and the diagonal map `Δ : Y → Y ×_S Y` is affine, then `g` is affine.
- Complete source proof: The base change `X ×_S Y → Y` of `X → S` by `Y → S` is affine since affine morphisms are stable under base change. The morphism `(1,g) : X → X ×_S Y` is the base change of `Δ : Y → Y ×_S Y` by the morphism `X ×_S Y → Y ×_S Y`. Hence, it is affine. Now the result follows since the composition of affine morphisms is affine.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem statement and proof placeholder for the later prover queue.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the generated source module is covered by the library target.
- `ShadowBench.lean`: imports `ShadowBench.Source` so plain project builds cover the generated target module.

## Import Plan

`ShadowBench/Source/Main.lean`
```lean
import Mathlib
```

## Suggested Search Modules

- `Mathlib.AlgebraicGeometry.Morphisms.Affine` for `AlgebraicGeometry.IsAffineHom`, composition of affine morphisms, and stability under base change (`isAffineHom_isStableUnderBaseChange`).
- `Mathlib.CategoryTheory.Limits.Shapes.Diagonal` for `CategoryTheory.Limits.pullback.diagonal`, `pullback.diagonalObj`, and diagonal/base-change API.
- `Mathlib.AlgebraicGeometry.Pullbacks` for scheme pullbacks and fiber-product notation/API.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`.
- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean`: identical candidate statements using ad hoc type-level schemes (`{S X Y : Type*} [Scheme S]`) and an undefined `IsSchemeMorphism`; rejected as Lean-invalid and not faithful to Mathlib's scheme category encoding, but they preserved the intended declaration name and informal theorem shape.
- `docs/skeletons/Skeleton4.lean`: same candidate with an extra malformed trailing `:= by sorry`; rejected for the same reasons.
- Final statement uses Mathlib objects `S X Y : Scheme`, morphisms `f : X ⟶ S`, `p : Y ⟶ S`, and `g : X ⟶ Y`, plus the over-`S` equality `g ≫ p = f`.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`.
- Source kind: theorem.
- Source title: `isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal`.
- Planned Lean declarations: `isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal` in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, theorem lines 17-18; proof environment lines 19-21 (proof text line 20).
- Skeleton candidate used: no skeleton copied; skeletons used only as naming and informal-shape hints.
- Dependencies:
  - `AlgebraicGeometry.Scheme` for schemes as objects of the category of schemes.
  - `CategoryTheory` morphism notation `X ⟶ Y` and composition `≫`.
  - `CategoryTheory.Limits.pullback.diagonal p` for the diagonal `Y ⟶ Y ×_S Y` of `p : Y ⟶ S`.
  - `AlgebraicGeometry.IsAffineHom` for affine morphisms.
  - Prover-side proof dependencies expected from source proof: base-change stability of `IsAffineHom`, the affine morphism instance for compositions, and the fact that the map `(1,g) : X ⟶ X ×_S Y` is the pullback/base change of the diagonal of `p`.
- Formal statement review:
  - Source has schemes `X`, `Y`, `S` and a morphism `g : X → Y` over `S`; Lean introduces structure morphisms `f : X ⟶ S` and `p : Y ⟶ S` and records `g` being over `S` by `w : g ≫ p = f`.
  - Source hypothesis "`X` is affine over `S`" is formalized as `hX : IsAffineHom f`.
  - Source hypothesis "the diagonal `Δ : Y → Y ×_S Y` is affine" is formalized as `hΔ : IsAffineHom (pullback.diagonal p)`.
  - Source conclusion "`g` is affine" is formalized as `IsAffineHom g`.
- Source qualifiers:
  - Mathematical object class: schemes `S`, `X`, and `Y`.
  - Quantifier order: choose structure morphisms `f : X ⟶ S`, `p : Y ⟶ S`, then `g : X ⟶ Y`, then the over-`S` condition and affine hypotheses.
  - Parameter domain/codomain: `f : X ⟶ S`, `p : Y ⟶ S`, `g : X ⟶ Y` in the category of schemes.
  - Equality/commutativity condition: `g ≫ p = f` expresses that `g` is a morphism over `S`.
  - Side conditions: `IsAffineHom f` and `IsAffineHom (pullback.diagonal p)`.
  - Output codomain/claim: `IsAffineHom g`.
  - Follow-on source-statement claims: none beyond the affine conclusion for `g`; the base-change, graph-map, and composition facts appear only in the source proof and are recorded below as prover notes.
- Lean coverage: exact source coverage, using Mathlib's categorical representation of schemes, morphisms over a base, fiber products, and diagonal morphisms.
  - The object-class qualifier is covered by `{S X Y : Scheme}`.
  - The morphism-over-`S` qualifier is covered by `f : X ⟶ S`, `p : Y ⟶ S`, `g : X ⟶ Y`, and `w : g ≫ p = f`.
  - The affine-over-`S` hypothesis on `X` is covered by `hX : IsAffineHom f`.
  - The diagonal-affineness hypothesis on `Y` is covered by `hΔ : IsAffineHom (pullback.diagonal p)`.
  - The conclusion is covered by `IsAffineHom g`.
  - The representation bridge for the source notation `Y ×_S Y` is Mathlib's `pullback.diagonalObj p`; the bridge for `Δ` is `pullback.diagonal p`.
- Scope changes: none. There is no mathematical weakening or strengthening; the only representation change is using Mathlib's standard categorical pullback object/morphism notation instead of a separately named fiber-product type.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Use the source proof literally. Build the projection `X ×_S Y ⟶ Y` as the base change of `f : X ⟶ S` along `p : Y ⟶ S` and infer it is affine from `hX`. Show the graph map `(1,g) : X ⟶ X ×_S Y` is a pullback/base change of `pullback.diagonal p`; infer it is affine from `hΔ`. Compose the graph map with the projection `X ×_S Y ⟶ Y` to identify `g`, then use closure of `IsAffineHom` under composition.

## Formalization Rules

```text
open CategoryTheory
open CategoryTheory.Limits

Formalize in Lean the theorem named `isAffineHom_of_isAffineHom_struct_of_isAffineHom_diagonal`:
Let `g : X → Y` be a morphism of schemes over `S`. If `X` is affine over `S` and the diagonal map `Δ : Y → Y ×_S Y` is affine, then `g` is affine.
```

## Formalization Proof-Ready Checklist

- [x] Source document and preflight manifest read.
- [x] Candidate skeletons compared against the source and Mathlib representation.
- [x] Blueprint source inventory contains `line-17` with complete source proof and prover notes.
- [x] Direct import plan records the generated Lean file imports and root aggregator imports.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Prover queue eliminated the planned `sorry` placeholder.
