# Formalization Blueprint: `algebraic-geometry/L3/alg_sche_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file draft containing proof skeleton `toGammaSpec` and source-facing alias `toΓSpec`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the generated target is covered by the root project module.
- `ShadowBench.lean`: imports `ShadowBench.Source` for the Lake default target.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
```

## Suggested Search Modules

- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Scheme.toSpecΓ`, `Scheme.toSpecΓ_apply`, `Scheme.toSpecΓ_appTop`, and locally ringed space `toΓSpec` lemmas.
- `Mathlib.AlgebraicGeometry.Scheme`: notation and basic global sections facts for schemes.
- `Mathlib.AlgebraicGeometry.StructureSheaf`: `StructureSheaf.toStalk`, `IsLocalRing.closedPoint`, and stalk/localization background if the proof needs to unfold the pointwise formula.

## Required Names

- `toΓSpec`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`: contains the requested name but models a scheme as `(X : Type u) [Scheme X]`, uses non-existent identifiers such as `StructureSheaf X` and `GlobalSections`, and omits a proof. Not adopted.
- `docs/skeletons/Skeleton2.lean` and `docs/skeletons/Skeleton3.lean`: add `by sorry` to the same non-elaborating statement shape as Skeleton1. Not adopted.
- `docs/skeletons/Skeleton4.lean`: compresses the same non-elaborating statement shape and also opens namespaces that do not exist in this project context. Not adopted.
- Final statement choice: use Mathlib's scheme object `X : Scheme`, global sections notation `Γ(X, ⊤)`, and the canonical morphism `X.toSpecΓ` from `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.

## Source Statement Inventory

### line-17

- Source inventory label: `line-17`
- Planned Lean declarations: `toGammaSpec`; source-facing alias `toΓSpec`.
- Source locator: `line-17`, `docs/source.tex`, theorem environment beginning at line 17, title `[toΓSpec]`.
- Source statement: Let `X` be a scheme. There is a canonical morphism `φ : X → Spec Γ(X)` from `X` to the spectrum of its global sections, and its underlying continuous map sends a point `x` to the prime ideal of global sections whose germs at `x` are not units in the stalk `𝒪_{X,x}`.
- Source proof text: Let `x ∈ X` and `U` be an affine open neighborhood of `x`. Consider the ring homomorphism `Γ(X) → Γ(U) → 𝒪_{X,x}` given by restriction and taking germs at `x`. Let `p = { s ∈ Γ(X) | s_x` is not a unit in `𝒪_{X,x} }`. We need to show that the induced map `φ^♯_x : (Γ(X) - p)^{-1} Γ(X) → 𝒪_{X,x}` is local. Let `t ∈ (Γ(X) - p)^{-1} Γ(X)` be `r/s` with `s ∉ p`. The proof claims that `t ∈ (Γ(X) - p)^{-1}p` iff its germ `t_x` is not a unit in `𝒪_{X,x}`. If `t` lies in the localized prime then `r ∈ p`, so `r_x` and hence `t_x` are non-units. Conversely, if `t_x` is not a unit, then `r_x` is not a unit and hence `r ∈ p` by definition.
- Dependencies:
  - `AlgebraicGeometry.Scheme.toSpecΓ`: canonical morphism `X ⟶ Spec Γ(X, ⊤)`.
  - `AlgebraicGeometry.Scheme.toSpecΓ_apply`: pointwise description of the underlying map.
  - `X.presheaf.Γgerm x`: germ map from global sections to the stalk at `x`.
  - `IsLocalRing.closedPoint`: the ideal of non-units in the local stalk, used as the target prime for the comap.
  - `Spec.map`: expresses the comap of prime ideals along the germ homomorphism.
- Formal statement review:
  - Source quantifies over an arbitrary scheme `X`; Lean uses `(X : Scheme.{u})`.
  - Source asserts existence of a canonical morphism to the spectrum of global sections; Lean states `∃ φ : X ⟶ Spec Γ(X, ⊤), φ = X.toSpecΓ ∧ ...`, explicitly identifying the witness with Mathlib's canonical unit morphism.
  - Source's pointwise prime ideal is formalized as `Spec.map (X.presheaf.Γgerm x) (IsLocalRing.closedPoint _)`, i.e. the comap of the stalk's closed point/nonunit ideal along the germ map from global sections.
  - The source proof's localness check is not a separate theorem statement; in Lean it is represented by using a morphism of schemes and recorded in the proof notes for the later prover.
- Source qualifiers:
  - Mathematical object class: arbitrary `Scheme`.
  - Quantifier order: `∀ X`, then existence of `φ`, then pointwise formula for every `x : X`.
  - Parameter domain: points of the underlying topological space of `X`.
  - Output codomain: `Spec Γ(X, ⊤)`, Mathlib's notation for the spectrum of the ring of global sections.
  - Equality/image condition: the underlying map of `φ` sends `x` to the comap prime `Spec.map (X.presheaf.Γgerm x) (IsLocalRing.closedPoint _)`.
  - Side conditions: none beyond `X` being a scheme and the stalks being local rings, supplied by the scheme/locally-ringed-space infrastructure.
  - Follow-on claims: source proof explains localness of the induced stalk map, but the theorem statement does not name an additional lemma.
- Lean coverage: intended full coverage of the source theorem statement. The proof skeleton `toGammaSpec` states existence of `φ : X ⟶ Spec Γ(X, ⊤)`, identifies `φ` with `X.toSpecΓ`, and gives the pointwise formula using `Spec.map (X.presheaf.Γgerm x) (IsLocalRing.closedPoint _)`. The source-facing alias `toΓSpec` preserves the document name. The representation bridge from “sections not mapping to units in the stalk” to Lean's `IsLocalRing.closedPoint` plus `Spec.map` is explicit in this entry and in the Lean doc comment.
- Scope changes: no intended statement-level weakening or strengthening. The proof-level localization argument is included as prover guidance rather than split into a separate source theorem because the source has only one theorem environment.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Prove the existential with witness `X.toSpecΓ`; the equality component is reflexive, and the pointwise component should follow from `Scheme.toSpecΓ_apply`. If unfolding is needed, use that `IsLocalRing.closedPoint` is the ideal of non-units in the local stalk and that `Spec.map` is comap along `X.presheaf.Γgerm x`, matching the source's prime `p`.

## Handoff Checklist

- [x] Source document and preflight manifest inspected.
- [x] Candidate skeletons compared against the source.
- [x] `line-17` source inventory entry recorded with statement, qualifiers, coverage, scope, and proof notes.
- [x] Target Lean file import block matches `## Import Plan`.
- [x] Root project module imports the generated target via `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
