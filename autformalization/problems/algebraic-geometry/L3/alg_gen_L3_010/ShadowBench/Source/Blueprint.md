# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_010`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Detected Theorem-Like Blocks

1. `line-17` (theorem, lines 17-19) - `isAffineOpen_inf_preimage`.

## Source Inventory

- Source inventory entry line-17: theorem `isAffineOpen_inf_preimage`, source lines 17-19, proof lines 19-25.
- Source inventory entry `line-17`: theorem `isAffineOpen_inf_preimage`, source lines 17-19, proof lines 19-25.
- Source inventory entry: line-17.
- Source inventory entry: `line-17`.
- Source block: line-17 (theorem, source lines 17-19; proof lines 19-25) — Lean declaration `isAffineOpen_inf_preimage`.

## Source Map

- `line-17` -> `isAffineOpen_inf_preimage`

## Source Statement Inventory

### line-17

- Kind: theorem.
- Title/name from source: `isAffineOpen_inf_preimage`.
- Source label: `line-17`.
- Source inventory label: `line-17`.
- Source locator: `docs/source.tex#line-17`, theorem block lines 17-19; proof lines 19-25.
- Source proof locator: `docs/source.tex`, proof lines 19-25.
- Source statement: Let `Y` be a separated scheme, and let `f : X → Y` be a morphism. For every affine open subset `U` of `X` and every affine open subset `V` of `Y`, `U ∩ f^{-1}(V)` is affine.
- Planned Lean declaration: `isAffineOpen_inf_preimage`
- Planned Lean declarations: `isAffineOpen_inf_preimage`
- Lean statement:
  ```lean
  theorem isAffineOpen_inf_preimage {X Y : Scheme} [Y.IsSeparated] (f : X ⟶ Y)
      (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
      IsAffineOpen (U ⊓ f ⁻¹ᵁ V) := by
    sorry
  ```
- Formal statement review: The Lean statement keeps the source quantifier order and mathematical content: separated target scheme `Y`, arbitrary source scheme `X`, morphism `f : X ⟶ Y`, affine opens `U : X.Opens` and `V : Y.Opens`, and conclusion that the open intersection `U ⊓ f ⁻¹ᵁ V` in `X` is affine. The Lean representation uses Mathlib's open-set API rather than a separate open-subscheme object, which is the intended bridge for affine opens.
- Direct dependencies: `Mathlib`; searched declarations include `AlgebraicGeometry.IsAffineOpen`, `AlgebraicGeometry.Scheme.IsSeparated`, `AlgebraicGeometry.Scheme.Hom.preimage_inf`, `AlgebraicGeometry.IsAffineOpen.inf`, and separated/graph closed-immersion infrastructure in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- Skeleton candidate used: Skeletons 1, 2, and 3 suggested the required theorem name and the intended shape `U ∩ f.pullback V`; Skeleton4 has a malformed duplicate `:= by sorry`. None of the skeleton API choices were copied because Mathlib represents schemes as objects `X Y : Scheme`, morphisms as `f : X ⟶ Y`, open subsets as `X.Opens`, separated schemes by `[Y.IsSeparated]`, affine opens by `IsAffineOpen`, inverse image of opens by `f ⁻¹ᵁ V`, and intersection by lattice inf `⊓`.
- Direct dependencies: `Mathlib`; searched declarations include `AlgebraicGeometry.IsAffineOpen`, `AlgebraicGeometry.Scheme.IsSeparated`, `AlgebraicGeometry.Scheme.Hom.preimage_inf`, `AlgebraicGeometry.IsAffineOpen.inf`, and separated/graph closed-immersion infrastructure in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- Source qualifiers:
  - Mathematical object class: schemes `X` and `Y`.
  - Side condition: `Y` is a separated scheme.
  - Morphism domain/codomain: `f : X ⟶ Y`.
  - Quantifier order: for every affine open `U` of `X`, for every affine open `V` of `Y`.
  - Output condition: the intersection of `U` with the inverse image of `V` under `f` is affine.
  - Equality/image condition: source notation `U ∩ f^{-1}(V)` is represented as the open-set lattice expression `U ⊓ f ⁻¹ᵁ V`.
  - Follow-on claims: none beyond affineness of this open subset.
- Lean coverage: full coverage of the source theorem in Mathlib's scheme API. The Lean hypotheses `hU : IsAffineOpen U` and `hV : IsAffineOpen V` express that `U` and `V` are affine open subsets. The conclusion `IsAffineOpen (U ⊓ f ⁻¹ᵁ V)` expresses affineness of `U ∩ f^{-1}(V)` as an open subscheme of `X`.
- Scope changes: no intentional mathematical weakening or strengthening. Representation bridge only: source schemes/morphisms/open subsets are encoded with Mathlib's `Scheme`, categorical morphism `⟶`, `Scheme.Opens`, `Scheme.Hom` open preimage notation `⁻¹ᵁ`, and lattice inf `⊓`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Let `p₁,p₂` be the projections of `X ×_ℤ Y`. The subspace `U ∩ f^{-1}(V)` is the image under `p₁` of `Γ_f(X) ∩ p₁^{-1}(U) ∩ p₂^{-1}(V)`. Now `p₁^{-1}(U) ∩ p₂^{-1}(V)` is identified with the underlying space of the scheme `U ×_ℤ V`, and is therefore an affine scheme. Since `Γ_f` is closed in `X ×_ℤ Y`, the intersection `Γ_f(X) ∩ p₁^{-1}(U) ∩ p₂^{-1}(V)` is closed in `U ×_ℤ V`. Consequently, the scheme induced by the subscheme of `X ×_ℤ Y` associated with `Γ_f`, on the open subset `Γ_f(X) ∩ p₁^{-1}(U) ∩ p₂^{-1}(V)` of its underlying space, is a closed subscheme of an affine scheme, hence is affine. The theorem then follows from the fact that `Γ_f` is an immersion.
- Prover notes: The source proof is graph-based: restrict the graph of `f` to `U ×_ℤ V`, use separatedness of `Y` to make the graph closed, use that a closed subscheme of the affine scheme `U ×_ℤ V` is affine, then transport affineness back along the graph immersion/projection identification. Mathlib search found related infrastructure around `IsSeparated.instIsClosedImmersionLiftSchemeId` and `IsAffineOpen.inf`; a proof run should first search for an existing lemma for affine intersection with inverse image over separated targets before expanding the graph argument.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.AlgebraicGeometry.Restrict`

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem declaration and proof placeholder.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the generated target is included in the project library.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the default `ShadowBench` target covers the generated source module.

## Required Names

- `isAffineOpen_inf_preimage`

## Formalization Rules from Instructions

```text
open CategoryTheory Opposite
open TopologicalSpace

/-
Formalize in Lean the Theorem (isAffineOpen_inf_preimage) from Text.

The theorem must be named `isAffineOpen_inf_preimage`.
   Matched text (candidate 0, theorem, label=isAffineOpen_inf_preimage): \begin{theorem}[isAffineOpen_inf_preimage] Let \(Y\) be a separated scheme, and let \(f:X\to
                                                                         Y\) be a morphism. For every affine open subset \(U\) of \(X\) and every affine open subset
                                                                         \(V\) of \(Y\), \(U\cap f^{-1}(V)\) is affine. \end{theorem}
-/
```
