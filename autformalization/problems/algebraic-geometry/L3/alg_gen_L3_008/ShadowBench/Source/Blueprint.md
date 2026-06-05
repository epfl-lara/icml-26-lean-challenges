# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_008`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains all generated declarations for this source document.
- `ShadowBench/Source.lean`: root project module, already imports `ShadowBench.Source.Main`, so project-level `lake build` covers the generated target module.

## Import Plan

```lean
import Mathlib
```

The target Lean file currently uses the single allowed direct import from `docs/instructions.md`. If later proofs replace `Mathlib` by narrower imports, update this block to match the target file exactly.

## Suggested Search Modules

These are search/proof hints only, not required direct imports while `import Mathlib` remains the target import.

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`, `Scheme.Hom.finiteType_appLE`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: finite affine covers of compact opens, quasi-compact morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `AlgebraicGeometry.IsImmersion` and the instance that immersions are locally of finite type.
- `Mathlib.AlgebraicGeometry.Noetherian` and `Mathlib.Topology.NoetherianSpace`: noetherian topological spaces and noetherian schemes.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` for the affine coordinate-ring condition in property (P).

## Required Names

- `FiniteType`
- `hasPropertyP_of_finiteType`
- `immersion_is_of_finiteType`

## Auxiliary Declarations

### `HasPropertyP`

- Purpose: formalizes the source's property (P) for a fixed affine open `W : Y.Opens`.
- Lean shape: for `f : X ⟶ Y` and affine `W`, `HasPropertyP f W hW` asserts that `f ⁻¹ᵁ W` is a finite supremum of affine opens `U` of `X`, and for every member of the finite cover the induced homomorphism `(f.appLE W U e).hom` is a `RingHom.FiniteType`.
- Source bridge: this is the direct Lean representation of the displayed condition (P), replacing the prose “finite union of affine open subsets” by a finite set of `X.affineOpens` whose supremum is the open preimage.

### `TopologicallyLocallyNoetherian`

- Purpose: records the theorem's “underlying space of `Y` is locally noetherian” assumption as a topological condition, since Mathlib's `AlgebraicGeometry.IsLocallyNoetherian` is a scheme/ringed-space condition.
- Lean shape: every point has an open neighborhood whose subspace is a `TopologicalSpace.NoetherianSpace`.
- Source bridge: avoids silently strengthening the source to a locally noetherian scheme. The second alternative in the theorem uses Mathlib's `NoetherianSpace X` for the source's “underlying space of `X` is noetherian”.

## Source Statement Inventory

Source inventory entries covered in this plan:

- `line-17`: Definition `[FiniteType]`, planned Lean declaration `FiniteType`.
- `line-30`: Theorem `[hasPropertyP_of_finiteType]`, planned Lean declaration `hasPropertyP_of_finiteType`.
- `line-37`: Theorem `[immersion_is_of_finiteType]`, planned Lean declaration `immersion_is_of_finiteType`.

### line-17

Source inventory entry `line-17`.

- Source inventory entry: `line-17`
- Planned Lean declarations: `FiniteType`.
- Source locator: `docs/source.tex`, lines 17--28.
- Source statement: A morphism `f : X → Y` is of finite type if `Y` is the union of affine opens `V_α` such that each preimage `f⁻¹(V_α)` is a finite union of affine opens `U_{α i}` and each `Γ(U_{α i}, O_X)` is a finitely generated algebra over `Γ(V_α, O_Y)`.
- Skeleton candidate used: Skeletons 1--4 suggested a `FiniteType` predicate but used an ill-typed unbundled scheme representation (`{X Y : Type*} [Scheme X] [Scheme Y]`). The final draft keeps the required name but uses Mathlib bundled schemes `X Y : Scheme` and morphisms `f : X ⟶ Y`.
- Dependencies: `HasPropertyP`, `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsAffineOpen`, `Scheme.Hom.appLE`, `RingHom.FiniteType`, finite sets of affine opens.
- Formal statement review: the Lean definition says there exists an index type `ι` and a family `V : ι → Y.affineOpens` whose supremum is `⊤`, and every `V i` satisfies `HasPropertyP f (V i) (V i).2`. This mirrors the source cover-by-affines definition rather than replacing it by the standard equivalent `QuasiCompact f ∧ LocallyOfFiniteType f`.
- Source qualifiers:
  - Mathematical object class: morphism of schemes.
  - Quantifier/order: existential affine open cover of the target.
  - Parameter domain: `X Y : Scheme`, `f : X ⟶ Y`.
  - Cover condition: the affine opens cover all of `Y`.
  - Property (P): each target affine preimage has a finite affine-open cover in `X`.
  - Ring condition: each induced map on sections is of finite type.
  - Follow-on terminology: `X` is a finite-type `Y`-scheme when `FiniteType f` holds.
- Lean coverage:
  - `X Y : Scheme` and `f : X ⟶ Y` cover the morphism-of-schemes object class.
  - `(⨆ i, (V i : Y.Opens)) = ⊤` covers the target-union condition.
  - `HasPropertyP` covers the finite affine preimage cover and section-ring finite-type algebra condition.
  - The follow-on “`Y`-scheme of finite type” terminology is represented by the predicate `FiniteType f` rather than a separate bundled over-category structure.
- Scope changes: no intended mathematical weakening. Representation changes: source unions are encoded as suprema of `Opens`; finite families are encoded as finite sets of `X.affineOpens`; finitely generated algebra is encoded by `RingHom.FiniteType` for the induced homomorphism on sections.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition only. For later equivalence-style proof work, Mathlib comments in `Morphisms/FiniteType.lean` note that “of finite type” is equivalent to locally of finite type plus quasi-compact; however this draft keeps the source cover definition directly.

### line-30

- Source inventory entry: `line-30`
- Planned Lean declarations: `hasPropertyP_of_finiteType`.
- Source locator: `docs/source.tex`, theorem lines 30--32, proof lines 32--35.
- Source statement: If `f : X → Y` is a morphism of finite type, then every open affine subset `W` of `Y` has property (P).
- Skeleton candidate used: Skeletons 1--4 suggested the theorem name and the idea of an affine open argument, but used an unbundled `Scheme` signature. The final draft keeps the source theorem name and uses `W : Y.Opens`, `hW : IsAffineOpen W`, and conclusion `HasPropertyP f W hW`.
- Dependencies: `FiniteType`, `HasPropertyP`, compactness/quasi-compactness of affine opens, distinguished/basic opens, localization finite type facts such as `RingHom.FiniteType` localization stability, finite unions of affine opens.
- Formal statement review: the Lean theorem quantifies over schemes `X Y`, a morphism `f : X ⟶ Y`, a proof `hf : FiniteType f`, and every affine open `W` of `Y`, then returns the exact property (P) predicate for `W`.
- Source qualifiers:
  - Mathematical object class: morphism of schemes.
  - Hypothesis: `f` is finite type in the source-cover sense.
  - Quantifier/order: for every open affine subset `W` of `Y`.
  - Output codomain: proposition `HasPropertyP f W hW`.
  - Equality/cover condition: finite affine cover of `f⁻¹(W)`.
  - Ring side condition: each induced section ring map is finite type.
- Lean coverage:
  - `hf : FiniteType f` covers the source finite-type hypothesis.
  - `(W : Y.Opens) (hW : IsAffineOpen W)` covers “every open affine subset”.
  - `HasPropertyP f W hW` covers all components of property (P), including finite affine cover and finite-type ring maps.
- Scope changes: no intended mathematical weakening. Representation changes are the same as for `HasPropertyP`: open subsets are Mathlib `Opens`, source finite unions are finite suprema, and finite-type algebra maps are `RingHom.FiniteType`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Let `W ⊆ Y` be an open affine. Then `W` is quasi-compact. Therefore, `W` is covered by finitely many distinguished opens `D(g_i) ⊆ V_{α(i)}`, `g_i ∈ Γ(V_{α(i)}, O_Y)`, where each `V_{α(i)}` belongs to the covering given by the definition. Fix one such distinguished open `D(g) ⊆ V_α`. By hypothesis, `f^{-1}(V_α)=⋃_j Z_j` with `Z_j` affine and `Γ(Z_j,O_X)` a finite type `Γ(V_α,O_Y)`-algebra. Let `φ_j : Γ(V_α,O_Y) → Γ(Z_j,O_X)` be the homomorphism induced by the restriction of `f` to `Z_j`, and put `g_j = φ_j(g)`. Then `f^{-1}(D(g)) ∩ Z_j = D(g_j)`, and `Γ(D(g_j),O_X) = Γ(Z_j,O_X)_{g_j} = Γ(Z_j,O_X)[1/g_j]`. Hence `Γ(D(g_j),O_X)` is a finite type algebra over `Γ(V_α,O_Y)[1/g] = Γ(D(g),O_Y)`. Thus `D(g)` has property (P). Since the `D(g_i)` form a finite affine cover of `W`, it follows that `W` itself has property (P).
- Prover notes: unfold `FiniteType` to obtain the source affine cover of `Y`; use compactness of the affine open `W` to reduce to finitely many basic opens inside members of that cover. For a basic open inclusion, refine the finite affine cover of the larger preimage by basic opens `D(g_j)` in the affine cover pieces, then use localization stability of `RingHom.FiniteType` to prove the finite-type section-ring condition. Combine the finite covers to build the finite set required by `HasPropertyP`.

### line-37

Source inventory entry `line-37`.

- Planned Lean declarations: `immersion_is_of_finiteType`.
- Source locator: `docs/source.tex`, theorem lines 37--39, proof lines 39--43.
- Source statement: Let `f : X → Y` be an immersion. If the underlying space of `Y` (respectively of `X`) is locally noetherian (respectively noetherian), then `f` is of finite type.
- Skeleton candidate used: Skeletons 1--4 suggested the theorem name and an immersion hypothesis. They strengthened/misrepresented the noetherian assumptions as scheme-typeclass assumptions and used unbundled schemes. The final draft keeps a bundled scheme morphism and states the source's two topological alternatives as a disjunction: `TopologicallyLocallyNoetherian Y ∨ NoetherianSpace X`.
- Dependencies: `FiniteType`, `HasPropertyP`, `AlgebraicGeometry.IsImmersion`, topological `NoetherianSpace`, the auxiliary `TopologicallyLocallyNoetherian`, finite affine covers of noetherian/compact opens, closed/open immersion factorization for immersions, quotient/localization finite-type ring homomorphisms.
- Formal statement review: the Lean theorem says an immersion `f : X ⟶ Y` is `FiniteType f` whenever either the underlying topological space of `Y` is locally noetherian or the underlying topological space of `X` is noetherian. This is intended to encode the source's “resp.” statement as two alternatives in one theorem.
- Source qualifiers:
  - Mathematical object class: morphism of schemes that is an immersion.
  - Hypotheses: either underlying `Y` is locally noetherian or underlying `X` is noetherian.
  - Quantifier/order: for arbitrary schemes `X Y` and morphism `f`.
  - Output codomain: `FiniteType f` in the source-cover sense.
  - Side condition: the noetherian assumptions are topological, not scheme-noetherian assumptions.
- Lean coverage:
  - `[IsImmersion f]` covers “`f` is an immersion”.
  - `TopologicallyLocallyNoetherian Y ∨ NoetherianSpace X` covers the two “resp.” topological alternatives.
  - `FiniteType f` covers the source finite-type conclusion using the definition entry `line-17`.
- Scope changes: no intended weakening. Representation changes: “resp.” is encoded by a disjunction; local noetherianity of the underlying space is encoded by the auxiliary pointwise-neighborhood predicate `TopologicallyLocallyNoetherian`; noetherianity of the underlying space is encoded by Mathlib's `NoetherianSpace`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: One may always suppose `Y` is affine by the lemma; if the underlying space of `Y` is locally noetherian, one may moreover suppose it is noetherian, since the underlying space of `X`, being a subspace of it, is then noetherian. Otherwise, one may suppose `Y` is affine and the underlying space of `X` noetherian; then `X` admits a finite covering by affine opens `D(g_i) ⊂ X`, `g_i ∈ Γ(Y,O_Y)`, each `X ∩ D(g_i)` being closed in `D(g_i)` (hence an affine scheme), since `X` is locally closed in `Y`. Therefore, `Γ(X ∩ D(g_i),O_Y)` is a finite type algebra over `Γ(D(g_i),O_Y)`, and thus `X ∩ D(g_i) → D(g_i)` is of finite type. Finally, `Γ(D(g_i),O_Y)=Γ(Y,O_Y)_{g_i}=Γ(Y,O_Y)[1/g_i]`, which is of finite type over `Γ(Y,O_Y)`, and this completes the proof.
- Prover notes: use `hasPropertyP_of_finiteType` locally on affine targets after reducing to the affine case. For an immersion into an affine noetherian/local-noetherian target, use the locally closed image to cover `X` by finitely many affine intersections with basic opens; each intersection is closed in a basic open and hence has coordinate ring a quotient of a localization of the base ring, so the section map is finite type. Under the `NoetherianSpace X` alternative, get the required finite affine cover directly from noetherian compactness of the underlying space. Under the locally noetherian `Y` alternative, reduce to noetherian affine neighborhoods so the locally closed subspace image is noetherian and again admits finite affine cover.

## Statement/Source Verification Gate

- The blueprint has been expanded from the preflight scaffold and contains entries for `line-17`, `line-30`, and `line-37`.
- Direct Lean imports in `## Import Plan` match the target file's import block.
- The root project module `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- The theorem statements are intentionally proof skeletons with `by sorry`; this formalizer pass stops before proof search.
- Next required action: run an independent statement/source verification pass. Only that review should change the statement verification statuses to `approved` if the Lean statements and source-proof notes are accepted.

## Suggested Proof Command After Review

After independent statement/source review approves or corrects the draft, start the proof queue with:

```text
/prove ShadowBench/Source/Main.lean
```
