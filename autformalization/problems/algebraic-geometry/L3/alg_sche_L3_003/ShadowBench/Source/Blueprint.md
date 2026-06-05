# Formalization Blueprint: `algebraic-geometry/L3/alg_sche_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: 2026-06-05 statement-fidelity review FIXED. The earlier draft trivialized the theorem (see below) and has been corrected to use a genuine relative-projective-space construction; the proof body is now `by sorry` (the deep properness fact is no longer assumed).

## 2026-06-05 Statement-Fidelity Review (FIXED)

The previous draft defined `IsRelativeProjectiveSpaceProjection n π := IsProper π` and built
`IsProjective f` around it, so the projection's properness — the entire substantive content of the
source theorem (that `ℙ^n_S → S` is proper) — was assumed as a hypothesis. As a result
`projective_isProper` was fully provable from "closed immersions are proper" plus composition
stability, and the committed proof closed with NO `sorry`. This is the trivialization pattern the
review flags as high risk.

Fix: replaced the bridge with the genuine construction (mirroring `alg_sche_L4_002`):
- `standardProjectiveSpace n := Proj 𝒜` for the standard `ℤ`-graded polynomial ring in `n+1` vars;
- `projectiveSpace n S` = base change of that absolute model along the terminal morphisms (`ℙ^n_S`);
- `IsProjective f := ∃ n i, IsClosedImmersion i ∧ i ≫ projectiveSpaceToBase n S = f`.

Now the conclusion `IsProper f` genuinely requires proving properness of `projectiveSpaceToBase`
(the universally-closed / Proj content), so the proof body is `by sorry`. Lean check passes
(exit 0, only `uses 'sorry'` warning). Expected name `projective_isProper` still resolves
(now at the root namespace, so the previous `export` line was removed as redundant/erroneous).


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

### `AlgebraicGeometry.standardProjectiveSpace`

- Source role: supplies the absolute projective-space model used to define `ℙ^n_S`.
- Lean declaration kind: implemented definition.
- Lean content: `Proj` of the standard graded polynomial ring over `ℤ` with `n + 1` homogeneous coordinates.
- Fidelity note: this is a concrete `Proj`-based bridge for projective space, not a predicate assuming properness.

### `AlgebraicGeometry.projectiveSpace`

- Source role: represents the relative projective space `ℙ^n_S`.
- Lean declaration kind: implemented definition.
- Lean content: base change of `standardProjectiveSpace n` along terminal morphisms, with projection `projectiveSpaceToBase n S := pullback.fst _ _`.
- Fidelity note: the construction preserves the source's projective-space object and leaves properness of the projection as proof content.

### `AlgebraicGeometry.IsProjective`

- Source role: formalizes the source phrase “`f : X → S` is a projective morphism”.
- Lean declaration kind: implemented definition, no construction gap.
- Lean content: `f` is projective when there exist `n : ℕ` and a morphism `i : X ⟶ projectiveSpace n S` such that `i` is a closed immersion and `i ≫ projectiveSpaceToBase n S = f`.
- Source qualifiers covered: existence of an integer `n ≥ 0` (as `n : ℕ`), closed immersion `i`, concrete relative projective-space target, and the factorization equality through the projection to `S`.
- Scope changes: Lean uses the project-local `Proj`/pullback construction `projectiveSpace n S` for `ℙ^n_S`; no properness certificate is bundled into the definition.

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
  - `AlgebraicGeometry.projectiveSpace`
  - `AlgebraicGeometry.projectiveSpaceToBase`
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
  - Factorization data: some `n : ℕ`, closed immersion `i : X ⟶ projectiveSpace n S`, and equality `i ≫ projectiveSpaceToBase n S = f`.
  - Standard facts invoked by the proof: the projection from projective space is proper; closed immersions are proper; proper morphisms are stable under composition.
  - Conclusion: `IsProper f`.
- Lean coverage: the theorem covers the scheme morphism, concrete projective-space factorization hypothesis through `projectiveSpace n S`, and properness conclusion. Properness of the projective-space projection is not assumed and remains the substantive proof obligation.
- Scope changes: Lean uses a project-local `Proj`/pullback construction for `ℙ^n_S`; the affine open cover by `D_+(x_i)` is proof content recorded in the source proof notes rather than a separate theorem statement.
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
  - Destructure `hf` into `n`, `i`, the closed-immersion proof, and the factorization equality.
  - Prove or import properness of `projectiveSpaceToBase n S`.
  - Use the existing instances/search results that closed immersions are finite/proper and that proper morphisms are stable under composition.
  - Rewrite the goal by the factorization equality, then prove properness of `i ≫ projectiveSpaceToBase n S` from properness of `i` and of the projective-space projection.

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
- [ ] Theorem proof obligation remains as `by sorry`; the deep projective-space-projection properness fact is not assumed by the statement.

## Suggested Next Command After Review

After independent statement/source review confirms the statement/source mapping or requests corrections, run:

```text
/prove ShadowBench/Source/Main.lean projective_isProper
```
