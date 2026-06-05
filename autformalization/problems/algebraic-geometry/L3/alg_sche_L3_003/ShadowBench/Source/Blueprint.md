# Formalization Blueprint: `algebraic-geometry/L3/alg_sche_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Inventory Entries

- Source inventory entry `line-17`: theorem `projective_isProper`, source `docs/source.tex:17-47`, Lean declaration `projective_isProper`.
- Source inventory entry: `line-17`
- Source label: `line-17`
- Source block id: `line-17`.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

These are search hints for the later prover, not direct imports required by the draft.

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`
- `Mathlib.CategoryTheory.MorphismProperty.Composition`

## Generated File Layout

- `ShadowBench/Source/Main.lean`: direct Mathlib import, local bridge definitions for projective morphisms of schemes, and the theorem skeleton `projective_isProper` with source-aware proof notes.
- `ShadowBench/Source.lean`: root project module; it already imports `ShadowBench.Source.Main`, so the generated target is covered by plain project builds.

## Required Names

- `projective_isProper`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose the required theorem name and the shape “projective hypothesis implies proper conclusion”, but they encode schemes as `(S X : Type*) [Scheme S] [Scheme X]`. In Mathlib, `AlgebraicGeometry.Scheme` is the category of schemes, so this typeclass encoding is not source-faithful or Lean-valid for this project.
- `docs/skeletons/Skeleton4.lean` has the same typeclass issue and is syntactically malformed by an extra `:= by sorry`.
- Adopted from the skeletons: only the required theorem name `projective_isProper` and the high-level predicate implication shape.
- Corrected draft shape: `{X S : Scheme} (f : X ⟶ S) (hf : AlgebraicGeometry.IsProjective f) : IsProper f`.

## Local Definition / Bridge Inventory

### `AlgebraicGeometry.IsRelativeProjectiveSpaceProjection`

- Source role: represents the standard fact used in the proof that the projection `π : ℙ^n_S ⟶ S` from relative projective space is proper.
- Lean declaration kind: implemented definition, no construction gap.
- Lean content: a bridge predicate on a candidate projection `π : P ⟶ S`, indexed by `n : ℕ`, defined as `IsProper π`.
- Reason for bridge: the Mathlib version available in this project has `Proj` and properness results for projective spectra, but the search did not find a concrete relative projective-space object `ℙ^n_S` or a built-in projective morphism property for arbitrary scheme morphisms.
- Fidelity note: this records the proof-relevant theorem about the relative projective-space projection, but it does not construct or identify the ambient scheme `P` with a concrete `ℙ^n_S`.

### `AlgebraicGeometry.IsProjective`

- Source role: formalizes the source phrase “`f : X → S` is a projective morphism”.
- Lean declaration kind: implemented definition, no construction gap.
- Lean content: `f` is projective when there exist `n : ℕ`, an ambient scheme `P`, a morphism `i : X ⟶ P`, and a projection `π : P ⟶ S` such that `i` is a closed immersion, `π` is certified by `IsRelativeProjectiveSpaceProjection n π`, and `i ≫ π = f`.
- Source qualifiers covered: existence of an integer `n ≥ 0` (as `n : ℕ`), closed immersion `i`, factorization through a projection to `S`, and properness of the projection as the standard projective-space fact used by the proof.
- Scope changes: the Lean bridge does not include a concrete relative projective-space construction `P = ℙ^n_S`; coverage is partial on the representation of the ambient projective space. The proof-relevant factorization data and properness certificate are retained.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source label: `line-17`
- Source block id: `line-17`
- Planned Lean declaration: `projective_isProper`
- Source locator: `docs/source.tex`, theorem lines 17-19; proof lines 19-47.
- Source statement: “Let `S` be a scheme, and let `f : X → S` be a projective morphism. Then `f` is proper.”
- Lean statement:

```lean
theorem projective_isProper {X S : Scheme} (f : X ⟶ S)
    (hf : AlgebraicGeometry.IsProjective f) : IsProper f
```

- Skeleton candidate used: Skeletons 1-3 informed the required name and implication shape, but their `Type*`/`[Scheme]` encoding was rejected. Skeleton 4 was rejected as malformed.
- Dependencies:
  - `AlgebraicGeometry.IsProjective`
  - `AlgebraicGeometry.IsRelativeProjectiveSpaceProjection`
  - `AlgebraicGeometry.IsClosedImmersion`
  - `AlgebraicGeometry.IsProper`
  - category composition `≫`
- Formal statement review:
  - The source quantifies over schemes `X` and `S`; Lean quantifies `{X S : Scheme}`.
  - The source morphism `f : X → S` is a scheme morphism; Lean uses `f : X ⟶ S`.
  - The source projective hypothesis is represented by the local bridge predicate `AlgebraicGeometry.IsProjective f`.
  - The source conclusion “`f` is proper” is exactly the Mathlib predicate `IsProper f`.
- Source qualifiers:
  - Mathematical object class: schemes `X` and `S`.
  - Morphism domain/codomain: `f : X ⟶ S`.
  - Hypothesis: `f` is projective via a finite-dimensional relative-projective-space factorization.
  - Factorization data: some `n : ℕ`, closed immersion `i : X ⟶ P`, projection `π : P ⟶ S`, and equality `i ≫ π = f`.
  - Standard facts invoked by the proof: the projection from projective space is proper; closed immersions are proper; proper morphisms are stable under composition.
  - Conclusion: `IsProper f`.
- Lean coverage: partial but explicit. The theorem covers the scheme morphism, projective-style factorization hypothesis, and properness conclusion. The concrete representation of the ambient object as `ℙ^n_S` is abstracted by `IsRelativeProjectiveSpaceProjection`.
- Scope changes: concrete relative projective space `ℙ^n_S` and its affine open cover by `D_+(x_i)` are not constructed in this draft because no project-local or Mathlib declaration for relative projective space over an arbitrary scheme was found. The bridge records the properness of the projection, which is precisely the projection fact used in the source proof.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
By definition, a morphism f : X to S is projective if there exists an integer n >= 0 and a closed immersion i : X -> P^n_S such that f factors as X -> P^n_S -> S, where pi is the structure morphism.

Thus it suffices to show that: (1) the morphism pi : P^n_S -> S is proper, and (2) proper morphisms are stable under composition and closed immersions.

First, the projection pi : P^n_S -> S is proper. Indeed, P^n_S is covered by finitely many affine opens of the form D_+(x_i) ≅ Spec(O_S[x_0/x_i, ..., x_n/x_i]), so pi is of finite type. It is separated because projective space is separated over the base. Finally, pi is universally closed; this follows from the fact that projective space over a base is universally closed (for instance, by the valuative criterion or by standard results on Proj). Hence pi is proper.

Second, closed immersions are proper morphisms. Indeed, a closed immersion is finite, hence proper.

Finally, proper morphisms are stable under composition. Therefore, since f = pi ∘ i is a composition of proper morphisms, it follows that f is proper.
```

- Prover notes:
  - Destructure `hf` into `n`, `P`, `i`, `π`, `hπ`, `hi`, and the factorization equality.
  - `hπ` unfolds through `IsRelativeProjectiveSpaceProjection` to `IsProper π`.
  - Use the existing instances/search results that closed immersions are finite and finite morphisms are proper, and that proper morphisms are stable under composition.
  - Rewrite the goal by the factorization equality `i ≫ π = f`, then prove properness of `i ≫ π` from `IsProper i` and `IsProper π`.

## Search Log

- `lean_search` for “AlgebraicGeometry IsProjective IsProper projective morphism proper” found `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsProper.stableUnderComposition`, and projective-spectrum properness results, but did not find a built-in scheme-morphism `IsProjective` predicate.
- `lean_search` for projective space over a scheme found affine space and `Proj` infrastructure, and external FormalConjecturesForMathlib hits for projective space, but no project-local Mathlib declaration for relative projective space `ℙ^n_S`.
- Content search in `Mathlib/AlgebraicGeometry` found no `IsProjective` or `ProjectiveSpace` declaration for scheme morphisms.

## Handoff Checklist

- [x] Source document inspected with theorem locator `line-17`.
- [x] Companion instructions, skeletons, manifest, and existing initial Lean files read.
- [x] Blueprint source inventory entry added for `line-17`.
- [x] Direct Lean import plan recorded and aligned with target Lean file.
- [x] Root module `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- [x] Lean declaration drafted with source proof/prover notes in the Lean doc comment.
- [x] Manual statement/source audit reviewed the bridge definitions, partial-coverage note, and theorem statement on 2026-06-04.
- [x] Theorem proof completed using properness of closed immersions and composition stability.

## Suggested Next Command After Review

After independent statement/source review confirms the statement/source mapping or requests corrections, run:

```text
/prove ShadowBench/Source/Main.lean projective_isProper
```
