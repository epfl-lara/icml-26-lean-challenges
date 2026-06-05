# Formalization Blueprint: `topology/L2/top_gen_L2_013`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Inventory Summary

The source document has two named items and no section headings:

1. `line-17`, Definition `IsLocallySurjective`, lines 17-19.
2. `line-21`, Theorem `locally_surjective_iff_surjective_on_stalks`, lines 21-28 including proof.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the final drafted source-backed definition and theorem skeleton.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target is included in the root `ShadowBench` library target.

No split into additional files is useful for this short source document.

## Import Plan

```lean
import Mathlib.Topology.Sheaves.LocallySurjective
```

The original instruction import block was used as the starting point. The direct import was tightened to `Mathlib.Topology.Sheaves.LocallySurjective` because it is the module containing the Mathlib source theorem and it transitively provides stalks, filtered-colimit preservation facts, and site-local surjectivity definitions used here.

## Suggested Search Modules

These are not direct imports unless a prover later needs them explicitly:

- `Mathlib.Topology.Sheaves.Stalks`
- `Mathlib.CategoryTheory.Limits.Preserves.Filtered`
- `Mathlib.CategoryTheory.Sites.LocallySurjective`

## Required Names

- `IsLocallySurjective`
- `locally_surjective_iff_surjective_on_stalks`

## Candidate Skeleton Review

- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` use `Set X` and a non-Mathlib-looking `Presheaf X`/`T : F → G` shape. They reflect the informal statement but are not directly compatible with Mathlib's `TopCat.Presheaf` API.
- `Skeleton4.lean` uses the Mathlib-compatible representation `X : TopCat`, `F G : X.Presheaf (Type u)`, and `T : F ⟶ G`. This skeleton shaped the final Lean declarations.
- The final definition is written explicitly in terms of `Opens X`, restriction maps `G.map (homOfLE hVU).op`, and sections of `F.obj (op V)`/`G.obj (op U)` to match the source definition directly rather than only naming Mathlib's bundled local-surjectivity predicate.
- Search found `TopCat.Presheaf.isLocallySurjective_iff` and `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` in `Mathlib.Topology.Sheaves.LocallySurjective`; these should guide the later proof.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source title: definition `IsLocallySurjective`.
- Planned Lean declaration: `IsLocallySurjective`
- Declaration kind: `def`
- Source locator: `docs/source.tex`, lines 17-19.
- Source statement: A map of presheaves `T : F → G` is locally surjective if for every open set `U`, every section `t ∈ G(U)`, and every point `x ∈ U`, there exists an open set `V` such that `x ∈ V ⊆ U` and a section `s ∈ F(V)` such that `T(s) = t|_V`.
- Lean statement:

```lean
def IsLocallySurjective {X : TopCat} {F G : X.Presheaf (Type u)} (T : F ⟶ G) : Prop :=
  ∀ (U : Opens X) (t : G.obj (op U)) (x : X), x ∈ U →
    ∃ (V : Opens X) (hVU : V ≤ U),
      (∃ (s : F.obj (op V)), T.app (op V) s = G.map (homOfLE hVU).op t) ∧ x ∈ V
```

- Skeleton candidate used: `docs/skeletons/Skeleton4.lean`, adjusted to avoid the non-existent `TopCat.Presheaf.stalkMap` notation and to remove unused binder warnings.
- Dependencies: `TopCat`, `Opens`, `Opposite.op`, category morphism notation `⟶`, `homOfLE`, and presheaf restriction maps from `Mathlib.Topology.Sheaves.LocallySurjective` and its transitive imports.
- Formal statement review: The Lean definition quantifies over an open `U`, a section `t` over `U`, a point `x`, the condition `x ∈ U`, a smaller open `V`, an inclusion proof `hVU : V ≤ U`, a section `s` over `V`, and the equality saying that `T` applied on `V` equals the restriction of `t` to `V`. The order and content match the source definition after translating open sets to `Opens X` and restrictions to `G.map (homOfLE hVU).op`.
- Source qualifiers:
  - Mathematical object class: type/set-valued presheaves on a topological space and a morphism of presheaves.
  - Quantifier order: open set `U`, section `t`, point `x`, membership `x ∈ U`, then existence of `V` and `s`.
  - Parameter domain: `U : Opens X`, `t : G.obj (op U)`, `x : X`.
  - Output codomain: proposition about the morphism `T`.
  - Equality/image condition: `T.app (op V) s = G.map (homOfLE hVU).op t`, the Lean version of `T(s) = t|_V`.
  - Side conditions: `x ∈ V` and `V ≤ U`.
  - Follow-on claims: none in the definition block.
- Lean coverage: Covered by `IsLocallySurjective` in `ShadowBench/Source/Main.lean`.
- Scope changes: Lean uses Mathlib's standard `TopCat`/`Opens` representation and type-valued presheaves `X.Presheaf (Type u)`. This matches the usual set-valued reading of the source. If the source is later read as arbitrary concrete-category-valued presheaves, this draft should be treated as the type-valued specialization rather than the fully general category-valued theorem.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: This is a definition, so no proof is present. For proving the theorem, the Mathlib bridge `TopCat.Presheaf.isLocallySurjective_iff` relates this pointwise shape to Mathlib's existing bundled predicate.

### line-21

- Source inventory entry: `line-21`
- Source title: theorem `locally_surjective_iff_surjective_on_stalks`.
- Planned Lean declaration: `locally_surjective_iff_surjective_on_stalks`
- Declaration kind: `theorem`
- Source locator: `docs/source.tex`, theorem lines 21-23 and proof lines 23-28.
- Source statement: A morphism `T : F → G` of presheaves is locally surjective if and only if for every point `x ∈ X`, the induced map on stalks `F_x → G_x` is surjective.
- Lean statement:

```lean
theorem locally_surjective_iff_surjective_on_stalks {X : TopCat} {F G : X.Presheaf (Type u)}
    (T : F ⟶ G) :
    IsLocallySurjective T ↔
      ∀ x : X, Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) x).map T) := by
  sorry
```

- Skeleton candidate used: `docs/skeletons/Skeleton4.lean`, with the induced stalk map written using Mathlib's actual functorial map `((TopCat.Presheaf.stalkFunctor (Type u) x).map T)` instead of the skeleton's unavailable `TopCat.Presheaf.stalkMap T x`.
- Dependencies: `IsLocallySurjective`, `TopCat.Presheaf.stalkFunctor`, `Function.Surjective`, and the Mathlib theorem `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` for the later proof.
- Formal statement review: The Lean theorem states the source equivalence for type-valued presheaves: the left side is the drafted local-surjectivity definition, and the right side quantifies over every point `x : X` and asserts surjectivity of the induced map on stalk objects produced by `stalkFunctor`.
- Source qualifiers:
  - Mathematical object class: type/set-valued presheaves `F G` on a topological space `X`, and a morphism of presheaves `T : F ⟶ G`.
  - Quantifier order: topological space `X`, presheaves `F G`, morphism `T`; equivalence whose right side then quantifies over every point `x : X`.
  - Parameter domain/codomain: the induced stalk map at each point, from the stalk of `F` at `x` to the stalk of `G` at `x`.
  - Equality/image conditions: left side is local surjectivity from `line-17`; right side is `Function.Surjective` for the induced map on stalks, i.e. every germ in `G_x` is in the image of a germ in `F_x`.
  - Side conditions: no sheaf condition; only a presheaf morphism and pointwise stalk maps are used.
  - Follow-on claims: none beyond the two directions of the equivalence.
- Lean coverage:
  - Local-surjectivity side: covered by `IsLocallySurjective T`, the definition drafted for `line-17`.
  - Pointwise stalk side: covered by `∀ x : X, Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) x).map T)`.
  - Equivalence: covered by theorem `locally_surjective_iff_surjective_on_stalks`.
- Scope changes: type-valued `TopCat.Presheaf (Type u)` is used rather than an arbitrary value category. This is an intentional specialization to the set-valued reading of sections and surjective functions; a fully general concrete-category-valued theorem is not claimed by this draft.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Suppose `T` is locally surjective. Let `x ∈ X` and let `g ∈ G_x` be a germ. Represent `g` as `⟨t, U⟩` for some open set `U ⊆ X` containing `x` and some section `t ∈ G(U)`. By local surjectivity, there exists an open set `V ⊆ U` containing `x` and a section `s ∈ F(V)` such that `T(s) = t|_V`. The germ of `s` at `x` maps to `⟨t|_V, V⟩ = g`, proving surjectivity on stalks. Conversely, suppose that for every `x ∈ X`, the induced map on stalks is surjective. Let `U ⊆ X` be an open set, `t ∈ G(U)`, and `x ∈ U`. The germ `t_x` of `t` at `x` is in `G_x`, so by surjectivity, there exists a germ `s_x ∈ F_x` mapping to `t_x`. Represent `s_x` as `⟨s, V⟩` for some open `V ⊆ X` containing `x` and some `s ∈ F(V)`. There exists an open set `W ⊆ V ∩ U` containing `x` such that `T(s)|_W = t|_W`. Thus, `T` is locally surjective.
- Prover notes: Use `TopCat.Presheaf.isLocallySurjective_iff` to translate the drafted `IsLocallySurjective` definition to Mathlib's bundled predicate, then use `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`. If proving directly, follow the source proof: use `germ_exist` to represent stalk elements by sections on neighborhoods; use local surjectivity to shrink in the forward direction; in the reverse direction use surjectivity of `((TopCat.Presheaf.stalkFunctor (Type u) x).map T)` on `G.germ U x hxU t`, represent the preimage germ by `F.germ_exist`, then use `germ_eq` to shrink so the restricted sections agree.

## Verification Notes

- Source document inspection: completed with `formalization_document_inspect` on `docs/source.tex`.
- Local/Mathlib search: completed with `lean_search`; key result is `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` in `Mathlib.Topology.Sheaves.LocallySurjective`.
- Draft target: `ShadowBench/Source/Main.lean`.
- Expected draft state: the theorem proof is intentionally a `by sorry` skeleton until independent source/statement review checks the statement.

## Handoff Checklist

- [x] Source document inspected.
- [x] Required ShadowBench instructions and skeletons read.
- [x] Blueprint source inventory entries recorded for `line-17` and `line-21`.
- [x] Lean declaration names match the required names.
- [x] Theorem proof notes are included in the Lean doc comment and in this blueprint.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Workflow handoff verifier has cleared the draft for proof work.
