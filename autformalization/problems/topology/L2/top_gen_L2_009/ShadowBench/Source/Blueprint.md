# Formalization Blueprint: `topology/L2/top_gen_L2_009`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the two source-backed declarations required by `docs/source.tex`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`, so the generated target is covered by the `ShadowBench` library build.

## Import Plan

```lean
import Mathlib.Topology.Sheaves.Sheafify
```

This is the direct Lean import used by `ShadowBench/Source/Main.lean`. It is required for `TopCat.Presheaf.sheafify`, `TopCat.Presheaf.stalkToFiber`, `TopCat.Presheaf.stalkToFiber_injective`, `TopCat.Presheaf.stalkToFiber_surjective`, and `TopCat.Presheaf.sheafifyStalkIso`. The module publicly imports the initially suggested `Mathlib.Topology.Sheaves.LocalPredicate` and `Mathlib.Topology.Sheaves.Stalks`.

## Suggested Search Modules

- `Mathlib.Topology.Sheaves.LocalPredicate`: local-predicate sheaf construction and stalk-to-fiber map for subsheaves.
- `Mathlib.Topology.Sheaves.Stalks`: definition and basic API for presheaf stalks.
- `Mathlib.Topology.Sheaves.Sheafify`: exact mathlib implementation of the source construction and stalk isomorphism.

## Required Names

- `stalkToFiber_injective`
- `sheafifyStalkIso`

## Source Inventory

1. `line-17` (definition, lines 17-23) - `stalkToFiber_injective`
   - Lean declaration: `stalkToFiber_injective`
   - Source inventory entry: `line-17`
2. `line-25` (theorem, lines 25-31; proof environment lines 33-49) - `sheafifyStalkIso`
   - Lean declaration: `sheafifyStalkIso`
   - Source inventory entry: `line-25`

## Source Inventory Entries

- Source inventory entry `line-17`: `stalkToFiber_injective` (definition), `docs/source.tex` lines 17-23.
- Source inventory entry `line-25`: `sheafifyStalkIso` (theorem), `docs/source.tex` statement lines 25-31 and proof environment lines 33-49.

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` suggest an unbundled `Presheaf α X` / `Sheaf α X` shape and a non-existent `germ.repr.data.snd x` projection. These were not adopted because they do not match the current Mathlib API for `TopCat.Presheaf` stalks and sheafification.
- `docs/skeletons/Skeleton4.lean` correctly suggests bundled `TopCat` and `X.Presheaf (Type v)`, but leaves a construction stub for the map. The final draft adopts its bundled `TopCat` universe shape and replaces the stub with Mathlib's canonical sheafification and stalk isomorphism.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source inventory label: `line-17`
- Source locator: `docs/source.tex`, lines 17-23.
- Source kind/title: Definition `[stalkToFiber_injective]`.
- Planned Lean declarations: `stalkToFiber_injective`.
- Lean signature: `def stalkToFiber_injective {X : TopCat.{v}} (F : Presheaf (Type v) X) : Sheaf (Type v) X`.
- Skeleton candidate used: `Skeleton4` for the bundled `TopCat` / `Presheaf (Type v)` parameter shape; Mathlib `TopCat.Presheaf.sheafify` for the actual construction.
- Dependencies: `TopCat.Presheaf.sheafify`; internally Mathlib defines it using `TopCat.Presheaf.Sheafify.isLocallyGerm`, `TopCat.subsheafToTypes`, and `TopCat.PrelocalPredicate.sheafify`.
- Formal statement review: the source defines the sheafification of a set-valued presheaf by assigning to each open set locally-germ-valued sections in the product of stalks and asserts that this assignment is a sheaf. The Lean declaration names this construction as required by the source label and returns Mathlib's canonical `Sheaf (Type v) X`, whose underlying presheaf is precisely the locally-germ subpresheaf of dependent functions into `F.stalk`.
- Source qualifiers:
  - Mathematical object class: topological space `X` and presheaf of sets `𝓕` on `X`.
  - Quantifier order: choose `X`, then a set-valued presheaf `F`; the construction is uniform in both.
  - Parameter domain: open subsets of `X` through the `TopCat` open-set category.
  - Output codomain: a sheaf of sets/types on `X`.
  - Equality/image condition: sections are families in the product of stalks locally equal to germs of sections of `F`.
  - Side condition: local neighborhood condition for each point in the open set.
  - Follow-on claim: the resulting presheaf is a sheaf and is called sheafification.
- Lean coverage: exact up to standard Mathlib representation. `X : TopCat.{v}` bundles the topological space, and `Presheaf (Type v) X` represents a set-valued presheaf. The codomain `Sheaf (Type v) X` records the sheaf property. Mathlib's `F.sheafify` uses the same locally-equal-to-germs construction described in the source.
- Scope changes: the source label `stalkToFiber_injective` names the sheafification definition even though Mathlib uses that name for the injectivity lemma. To preserve the required declaration name without redefining Mathlib internals, the draft provides a top-level `def` with the source-required name for `F.sheafify`. The unbundled phrase “topological space” is represented by bundled `TopCat`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: this source block is a definition, not a proof. The construction should unfold to `TopCat.Presheaf.sheafify`; later proofs can use Mathlib lemmas about `F.sheafify`, especially `TopCat.Presheaf.stalkToFiber`, `TopCat.Presheaf.stalkToFiber_injective`, and `TopCat.Presheaf.stalkToFiber_surjective`.

### line-25

- Source inventory entry: `line-25`
- Source inventory label: `line-25`
- Source locator: `docs/source.tex`, statement lines 25-31; proof environment lines 33-49.
- Source kind/title: Theorem `[sheafifyStalkIso]`.
- Planned Lean declarations: `sheafifyStalkIso`.
- Lean signature: `def sheafifyStalkIso {X : TopCat.{v}} (F : Presheaf (Type v) X) (x : X) : (stalkToFiber_injective F).presheaf.stalk x ≅ F.stalk x`.
- Skeleton candidate used: `Skeleton4` for the bundled stalk-isomorphism shape; final codomain is an explicit isomorphism `≅` rather than a theorem about a stubbed map.
- Dependencies: `stalkToFiber_injective`, `TopCat.Presheaf.sheafifyStalkIso`, `TopCat.Presheaf.stalkToFiber`, `TopCat.Presheaf.stalkToFiber_injective`, `TopCat.Presheaf.stalkToFiber_surjective`.
- Formal statement review: the source says that, for each `x : X`, the obvious map from the stalk of the sheafification to the original stalk, sending a germ represented by `(U, s)` to the value `s(x)` in the original stalk, is an isomorphism. The Lean declaration returns Mathlib's canonical isomorphism from `(stalkToFiber_injective F).presheaf.stalk x` to `F.stalk x`; its forward morphism is Mathlib's `stalkToFiber`, the stalk-to-fiber/evaluation map described by the source.
- Source qualifiers:
  - Mathematical object class: topological space `X`, set-valued presheaf `F`, and its sheafification `\widetilde F`.
  - Quantifier order: `X`, then `F`, then point `x : X`.
  - Parameter domain: a point `x` of the underlying topological space.
  - Output codomain: an isomorphism between stalks `\widetilde F_x` and `F_x`.
  - Equality/image condition: the forward map evaluates a representative section of the sheafification at the point, i.e. `(U, s) ↦ s(x)` / `stalkToFiber`.
  - Side conditions: the source uses the local-germ definition of sheafification from `line-17`; no extra separation or sheaf assumptions on `F`.
  - Follow-on claims: source proof establishes surjectivity and injectivity of the obvious map.
- Lean coverage: exact up to standard Mathlib representation. The source's `\widetilde F` is represented by the top-level alias `stalkToFiber_injective F = F.sheafify`. Stalks are Mathlib presheaf stalks. Returning an isomorphism `≅` records the source claim that the obvious map is an isomorphism.
- Scope changes: the source theorem is formalized as a named Lean `def` returning an isomorphism, following Mathlib's `TopCat.Presheaf.sheafifyStalkIso`, rather than as a `theorem : IsIso φ` about a separately stubbed map. This changes the Lean representation of the statement but not the mathematical content. The source's unbundled `x ∈ X` is represented by `x : X` for bundled `TopCat`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: “We prove the surjectivity first. Let `(U,s) ∈ 𝓕_x` be given where `U` is an open neighborhood of `x` and `s ∈ 𝓕(U)`. Then, `t := (s_y)_{y ∈ U} ∈ \widetilde F(U)` and we have `(U,t) ∈ \widetilde F_x` which is mapped to `(U,s)` under `φ_x` since `t(x) = s_x = (U,s)`. For injectivity, suppose we have `(U,s), (V,t) ∈ \widetilde{𝓕}_x` such that `s(x) = t(x)`. By definition of the sheafification, there exist open neighborhoods `U' ⊆ U`, `V' ⊆ V` of `x` and sections `s' ∈ 𝓕(U')`, `t' ∈ 𝓕(V')` such that `s'_y = s(y)` for all `y ∈ U'` and `t'_z = t(z)` for all `z ∈ V'`. Thus `(U',s') = s'_x = s(x) = t(x) = t'_x = (V',t')`, so there exists an open neighborhood `W ⊆ U' ∩ V'` of `x` such that `s'|_W = t'|_W`. Then for any `y ∈ W`, `s(y) = s'_y = (W,s') = (W,t') = t'_y = t(y)`, so the two sections of `\widetilde{𝓕}` agree on `W`. Therefore `(U,s) = (W,s|_W) = (W,t|_W) = (V,s)`, and the map `φ_x` is injective.”
- Source proof transcription note: the final displayed equality in the source has `(V,s)`. This appears to be a source typo for `(V,t)` because `t` is the section over `V`; the Lean statement does not depend on this typo, and the prover notes use the mathematically intended equality of germs after restriction.
- Prover notes: Mathlib's proof follows the source proof exactly. For surjectivity use `TopCat.Presheaf.stalkToFiber_surjective`, which builds the family of germs from a representative section. For injectivity use `TopCat.Presheaf.stalkToFiber_injective`, which localizes representatives, applies `F.germ_eq`, and then proves equality on a smaller open neighborhood. The final isomorphism is `TopCat.Presheaf.sheafifyStalkIso F x`.

## Formalization Rules

```text
open TopCat Opposite TopologicalSpace CategoryTheory

Formalize in Lean the following named items from Text.

1. Definition (stalkToFiber_injective)
   The definition must be named `stalkToFiber_injective`.
2. Theorem (sheafifyStalkIso)
   The theorem must be named `sheafifyStalkIso`.

Every listed named item must be formalized with exactly the stated Lean name.
```

## Draft Readiness Notes

- Source document and preflight manifest were inspected.
- Local project instructions and all candidate skeletons were inspected.
- Mathlib search found the exact construction and stalk-isomorphism API in `Mathlib.Topology.Sheaves.Sheafify`.
- The source inventory entries `line-17` and `line-25` are populated for reviewer inspection.
- The independent statement/source verification pass still needs to review and stamp the two source entries.
