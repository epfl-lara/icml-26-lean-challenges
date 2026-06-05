# Formalization Blueprint: `topology/L2/top_gen_L2_011`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file formalization draft for the two source-backed items. The project root imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so plain project builds cover the target module.

## Import Plan

```lean
import Mathlib.Topology.VectorBundle.Hom
```

## Suggested Search Modules

- `Mathlib.Topology.VectorBundle.Hom`: imported directly; provides Mathlib's Hom-bundle vector-bundle instance with the source theorem name.
- `Mathlib.Topology.VectorBundle.Basic`: useful search module for the general `VectorBundle` API.
- `Mathlib.Analysis.Normed.Module.Basic`: useful search module for normed module/typeclass facts if later proof work needs them.

## Search and Skeleton Review

- Local/Mathlib search found `Bundle.ContinuousLinearMap.vectorBundle` in `Mathlib.Topology.VectorBundle.Hom`; this is the relevant upstream theorem/instance for the source Hom-bundle theorem.
- The final draft follows Mathlib's dependent-family vector-bundle representation: a bundle over `B` is represented by a family `E : B → Type*`, with total space `Bundle.TotalSpace F E`, not by a separate total-space projection map.
- The companion skeleton files were treated as suggestions only. The source definition title `continuousLinearMap` is implemented locally as the Hom-bundle fiber family. The source theorem title is already occupied by Mathlib's imported declaration, so the local proof obligation is named `homBundle_vectorBundle_statement` while the blueprint records that Mathlib supplies the exact source theorem name.

## Source Statement Inventory

### line-17

- Title: Definition `continuousLinearMap`.
- Planned Lean declarations: `continuousLinearMap`
- Declaration kind: noncomputable definition in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, lines 17-19.
- Source statement: Let `E₁`, `E₂` be vector bundles over a base space `B` with fibers `F₁`, `F₂`, respectively, where `Fᵢ` is a normed space over a normed field `kᵢ`, for `i = 1,2`. Let `σ : k₁ → k₂` be an isometric ring homomorphism. The Hom-bundle `Hom_σ(E₁,E₂)` is defined to be a vector bundle over `B` whose fiber `Hom_σ(E₁,E₂)_x` is defined as the space of `σ`-semilinear maps between `(E₁)_x` and `(E₂)_x`.
- Skeleton candidate used: none adopted verbatim; the final definition follows Mathlib's semilinear continuous-map notation and the source fiber formula.
- Dependencies: `ContinuousLinearMap`; notation `E₁ x →SL[σ] E₂ x`; normed-field parameters `𝕜₁`, `𝕜₂`; ring homomorphism parameter `σ`; theorem entry `line-21` for the vector-bundle structure bridge.
- Formal statement review: The Lean definition states the underlying Hom-bundle family as `fun x => E₁ x →SL[σ] E₂ x`. This exactly matches the source's fiber description. The source phrase saying the Hom-bundle is “defined to be a vector bundle” is represented in two Lean layers: this definition supplies the fiber family, and the theorem entry `line-21` supplies the `VectorBundle` structure on that family. The definition therefore has exact coverage for fibers and partial-by-design coverage for the whole vector-bundle object, with the bridge made explicit by `line-21`.
- Source qualifiers:
  - mathematical object class: Hom-bundle associated to two vector bundles over the same base;
  - quantifier order: normed fields `𝕜₁`, `𝕜₂`, isometric ring homomorphism `σ`, base space `B`, input bundle families `E₁`, `E₂`;
  - parameter domain: source `σ : 𝕜₁ → 𝕜₂` is an isometric ring homomorphism; the model fibers are normed spaces over the respective normed fields; the input fibers carry the topological additive and module structures needed for continuous semilinear maps;
  - output codomain: source object is a vector bundle over `B`; Lean represents its underlying fiber family over `B` whose fiber at `x` is the type of `σ`-semilinear continuous maps from `E₁ x` to `E₂ x`;
  - equality/image condition: `Hom_σ(E₁,E₂)_x = E₁ x →SL[σ] E₂ x`;
  - side conditions: vector-bundle assumptions on `E₁` and `E₂`, and the isometry condition on `σ`, are not needed to define the bare fiber family but are asserted in the theorem entry `line-21`;
  - follow-on claim: the defined family carries a natural vector-bundle structure, formalized in `line-21`.
- Lean coverage:
  - fiber equality/family: `continuousLinearMap σ E₁ E₂` unfolds to `fun x => E₁ x →SL[σ] E₂ x`;
  - parameter coverage: the definition is stated for any ring homomorphism `σ`, so the source isometric case is covered by specialization; the isometry assumption is reintroduced where vector-bundle structure is claimed;
  - vector-bundle structure: covered by the source theorem entry `line-21`.
- Scope changes: Lean uses Mathlib's dependent-family representation rather than a bundled projection map for total spaces. The definition is slightly generalized from isometric ring homomorphisms to arbitrary ring homomorphisms for the fiber-family layer. The phrase “defined to be a vector bundle” is split between the local fiber-family definition and the theorem/instance giving the vector-bundle structure; this is an explicit representation bridge, not a weakening of the source object class.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: There is no separate source proof for this definition. For later theorem proving, unfold `continuousLinearMap`; its fiber at `x` is definitionally `E₁ x →SL[σ] E₂ x`.

### line-21

- Title: Theorem `Bundle.ContinuousLinearMap.vectorBundle`.
- Planned Lean declarations: `homBundle_vectorBundle_statement`
- Declaration kind: theorem in `ShadowBench/Source/Main.lean`.
- Imported source-name coverage: Mathlib already provides the theorem/instance named Bundle.ContinuousLinearMap.vectorBundle from the direct import `Mathlib.Topology.VectorBundle.Hom`.
- Source locator: `docs/source.tex`, theorem lines 21-23 and proof lines 23-54.
- Source statement: Let `E₁`, `E₂` be vector bundles over a base space `B` with fibers `F₁`, `F₂`, respectively, where `Fᵢ` is a normed space over a normed field `kᵢ`, for `i = 1,2`. Let `σ : k₁ → k₂` be an isometric ring homomorphism. The Hom-bundle `Hom_σ(E₁,E₂)` inherits the natural structure of a vector bundle.
- Skeleton candidate used: none adopted verbatim; the final theorem follows the upstream Mathlib Hom-bundle theorem/instance and uses the local source-facing alias `continuousLinearMap`.
- Dependencies: local definition `continuousLinearMap`; `VectorBundle`; `FiberBundle`; `RingHomIsometric`; `ContinuousLinearMap`; Mathlib technical target-fiber assumptions `[∀ x, IsTopologicalAddGroup (E₂ x)]` and `[∀ x, ContinuousSMul 𝕜₂ (E₂ x)]`; imported Mathlib Hom-bundle instance with the source theorem name.
- Formal statement review: The Lean theorem assumes two Mathlib vector bundles `E₁` and `E₂` over the same base, model fibers `F₁` and `F₂`, and an isometric scalar ring homomorphism `σ`. It concludes `VectorBundle 𝕜₂ (F₁ →SL[σ] F₂) (continuousLinearMap σ E₁ E₂)`, i.e. the Hom-bundle family has model fiber the continuous semilinear maps from `F₁` to `F₂` and scalar field `𝕜₂`. This is the source theorem in Mathlib's dependent-family representation. The exact source theorem name is imported from Mathlib, and the local theorem is a proof-queue companion using the source alias. The extra target-fiber topological group and continuous-scalar-action assumptions are Mathlib API requirements for constructing the Hom-bundle topology, not additional mathematical content beyond the source phrase “vector bundle”.
- Source qualifiers:
  - mathematical object class: natural vector-bundle structure on the Hom-bundle of two vector bundles over the same base;
  - quantifier order: normed fields `𝕜₁`, `𝕜₂`, isometric ring homomorphism `σ`, base topological space `B`, model fibers `F₁`, `F₂`, bundle fiber families `E₁`, `E₂`, vector-bundle assumptions on both inputs;
  - parameter domain: `σ` is an isometric ring homomorphism; the model fibers are normed spaces over the respective normed fields; the input bundles are vector bundles over the common base;
  - output codomain: `VectorBundle 𝕜₂ (F₁ →SL[σ] F₂) (continuousLinearMap σ E₁ E₂)`;
  - equality/image condition: the Hom-bundle fiber at `x` is `E₁ x →SL[σ] E₂ x`, and the model fiber is `F₁ →SL[σ] F₂`;
  - side conditions: continuity of local trivializations and transition maps is represented by Mathlib's `FiberBundle`/`VectorBundle` assumptions and Hom-bundle theorem; Mathlib also requires target-fiber topological additivity and continuous `𝕜₂`-scalar multiplication instances;
  - follow-on claims: operator norm, scalar multiplication, local trivializations, and conjugation transition maps occur in the source proof/naturality explanation rather than as separate source theorem conclusions.
- Lean coverage:
  - Hom-bundle family/fiber equality: conclusion uses `continuousLinearMap σ E₁ E₂`, which unfolds to `fun x => E₁ x →SL[σ] E₂ x`;
  - model fiber: `F₁ →SL[σ] F₂`, matching source `Hom_σ(F₁,F₂)`;
  - scalar field: `𝕜₂`, matching the source scalar multiplication `(a · f)(m) = a · f(m)`;
  - vector-bundle structure: conclusion is the Mathlib `VectorBundle` typeclass claim;
  - technical assumptions: the Lean statement includes `NontriviallyNormedField` scalar fields, `FiberBundle`/`VectorBundle` input bundle instances, and Mathlib's target-fiber topological additivity/continuous-smul assumptions needed by `Bundle.ContinuousLinearMap.vectorBundle`;
  - exact source theorem name: supplied by the imported Mathlib declaration, while the local theorem skeleton is named `homBundle_vectorBundle_statement` to avoid redeclaration conflict.
- Scope changes: Lean uses a dependent family `E : B → Type*` and `Bundle.TotalSpace F E` instead of an arbitrary total-space projection notation. Lean requires `NontriviallyNormedField` because this is Mathlib's standard vector-bundle scalar-field assumption. Lean also exposes target-fiber `IsTopologicalAddGroup` and `ContinuousSMul` assumptions used by the Hom-bundle construction; these are recorded technical assumptions associated with the target vector-bundle fibers. The source's “natural structure” is formalized as the `VectorBundle` typeclass instance. The local theorem name differs only because the exact source name already exists in the imported Mathlib namespace.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

  ```text
  For each x ∈ B, the fiber Hom_σ(E_1,E_2)_x is the space of σ-semilinear maps between (E_1)_x and (E_2)_x. There exist an operator norm of semilinear maps and a scalar multiplication

      (a · f)(m) = a · f(m),    a ∈ k_2, f ∈ Hom_σ(E_1,E_2)_x, m ∈ (E_1)_x

  so that Hom_σ(E_1,E_2)_x has the natural structure of a normed space over k_2.

  Now we define local trivializations. Let

      e_1 : E_1|_{U_1} ≃ U_1 × F_1,    e_2 : E_2|_{U_2} ≃ U_2 × F_2

  be local trivializations of E_1,E_2, respectively, for open subsets U_1,U_2 ⊆ B. Then we define a local trivialization of the Hom-bundle over U := U_1 ∩ U_2 by

      e : Hom_σ(E_1,E_2)|_U ≃ U × Hom_σ(F_1,F_2),
          (x,T) ↦ (x,(e_2)_x ∘ T ∘ (e_1)_x^{-1})

  for x ∈ B, T ∈ Hom_σ(E_1,E_2)_x, where (e_i)_x = e_i|_{(E_i)_x} : (E_i)_x ≃ F_i, i=1,2 are linear isomorphisms.

  For transition maps, let e,e' be local trivializations of the Hom-bundle over U,U', respectively, which are induced by the pairs of local trivializations (e_1,e_2),(e_1',e_2'). For each i=1,2, we have transition maps

      g_i : U_i ∩ U_i' → GL(F_i)

  where g_i is induced from the composition

      (U_i ∩ U_i') × F_i ≃[e_i^{-1}] E_i|_{U_i ∩ U_i'} ≃[e_i] (U_i ∩ U_i') × F_i

  of the bundle E_i. Now for the Hom-bundle, define the transition map as

      g : U ∩ U' → GL(Hom_σ(F_1,F_2)),
          x ↦ (S ↦ g_2(x) ∘ S ∘ g_1(x)^{-1}).

  By construction, local trivializations and transition maps of the Hom-bundle above are continuous and define the natural vector-bundle structure on the Hom-bundle.
  ```
- Source proof / prover notes: The local theorem should not rebuild the local-trivialization construction from scratch. Unfold `continuousLinearMap` and use the imported Hom-bundle vector-bundle instance supplied by `Mathlib.Topology.VectorBundle.Hom`. The source proof explains why that instance is natural: fibers use the operator norm and `𝕜₂`-scalar multiplication, local trivializations conjugate a fiber map by the source and target trivializations, and transition maps act by `S ↦ g₂ x ∘ S ∘ g₁ x⁻¹`.

## Handoff Checklist

- [x] Source document inspected with theorem-like blocks `line-17` and `line-21` recorded.
- [x] Candidate skeletons compared against the source and Mathlib API.
- [x] Local/Mathlib search used for the Hom-bundle vector-bundle theorem.
- [x] Direct Lean imports recorded and aligned with `ShadowBench/Source/Main.lean`.
- [x] Root project module covers `ShadowBench.Source.Main` via `ShadowBench/Source.lean`.
- [x] Lean draft contains stable declarations with source-aware doc comments.
- [x] Project-level Lean verification passed with the expected draft `sorry` warning.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Prover queue has eliminated all `sorry` placeholders in the target file.
