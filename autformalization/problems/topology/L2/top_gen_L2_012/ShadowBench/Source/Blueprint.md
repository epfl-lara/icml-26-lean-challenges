# Formalization Blueprint: `topology/L2/top_gen_L2_012`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one-file formalization for the skyscraper presheaf construction and its sheaf-property theorem skeleton.
- `ShadowBench/Source.lean`: root submodule aggregator importing `ShadowBench.Source.Main`.
- `ShadowBench.lean`: project root importing `ShadowBench.Source`.

## Import Plan

```lean
import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Functors
```

These are the direct Lean imports used by `ShadowBench/Source/Main.lean`.

## Suggested Search Modules

- `Mathlib.Topology.Sheaves.Skyscraper`: contains the corresponding Mathlib construction `skyscraperPresheaf`, the pushforward comparison theorem of the same mathematical idea, and the proof pattern for the sheaf theorem.
- `Mathlib.Topology.Sheaves.PUnit`: one-point-space sheaf criterion used in the source proof.
- `Mathlib.Topology.Sheaves.Functors`: pushforward of sheaves preserves the sheaf condition.

## Required Names

- `skyscraperPresheaf_eq_pushforward`
- `skyscraperPresheaf_isSheaf`

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source title: definition `skyscraperPresheaf_eq_pushforward`.
- Planned Lean declaration: `skyscraperPresheaf_eq_pushforward`
- Declaration kind: `def`
- Source locator: `docs/source.tex`, lines 17-20.
- Source statement: Let `X` be a topological space, `p₀ ∈ X`, `C` a category with a terminal object, and `A : C`. A skyscraper sheaf/presheaf with value `A` is a presheaf on `X` valued in `C` sending an open `U` to `A` when `p₀ ∈ U` and to a terminal object `1_C` when `p₀ ∉ U`.
- Lean statement:
  ```lean
  def skyscraperPresheaf_eq_pushforward {X : TopCat.{u}} (p₀ : X)
      {C : Type v} [Category.{w} C] [HasTerminal C] (A : C) : Presheaf C X
  ```
- Skeleton candidate used: shaped by `docs/skeletons/Skeleton4.lean`, because it uses `TopCat`, `HasTerminal C`, and returns a concrete presheaf. Skeletons 1-3 were rejected as final statements because they encode a predicate on a presheaf and use `default` for the terminal object, which does not faithfully represent an arbitrary categorical terminal object.
- Dependencies: `TopCat`, `Presheaf`, `Opens`, `Opposite.unop`, `CategoryTheory.Limits.HasTerminal`, `terminal C`, `terminalIsTerminal`.
- Formal statement review: the source describes the skyscraper presheaf by its values on opens. The Lean declaration constructs that presheaf directly: the object value is `if p₀ ∈ U then A else terminal C`, and restriction maps are identity/equality morphisms over opens containing `p₀` and terminal morphisms otherwise.
- Source qualifiers:
  - Object class: topological space `X`, point `p₀`, category `C` with terminal object, object `A : C`, presheaf on `X` valued in `C`.
  - Quantifier order: `X`, `p₀`, `C`, terminal structure, `A`.
  - Parameter domain: opens of `X`.
  - Output codomain: `Presheaf C X`.
  - Equality/value condition: value is `A` on opens containing `p₀`; value is a terminal object on opens not containing `p₀`.
  - Side conditions: restriction maps must be well-defined functorial maps for the presheaf.
- Lean coverage: the declaration type covers the presheaf object class and parameters; the implementation covers the two value cases using `terminal C` and supplies the functorial restriction maps.
- Scope changes: represents the source definition as the canonical constructed skyscraper presheaf rather than as a predicate on an arbitrary presheaf `F`. This is a representation choice; a later review should confirm it is acceptable for the theorem statement.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no proof in the source definition. The key implementation obligation is construction, not a theorem proof; no `sorry` is left in this definition.

### line-22

- Source inventory entry: `line-22`
- Source title: theorem `skyscraperPresheaf_isSheaf`.
- Planned Lean declaration: `skyscraperPresheaf_isSheaf`
- Declaration kind: `theorem`
- Source locator: `docs/source.tex`, theorem lines 22-24; proof lines 24-38.
- Source statement: A skyscraper presheaf with value `A` is a sheaf.
- Lean statement:
  ```lean
  theorem skyscraperPresheaf_isSheaf {X : TopCat.{u}} (p₀ : X)
      {C : Type v} [Category.{w} C] [HasTerminal C] (A : C) :
      (skyscraperPresheaf_eq_pushforward p₀ A).IsSheaf
  ```
- Skeleton candidate used: shaped by `docs/skeletons/Skeleton4.lean`, adjusted so the definition is implemented rather than a construction `sorry`, and so the theorem targets the implemented canonical skyscraper presheaf. Skeletons 1-3 were not adopted because their predicate formulation used a noncanonical `default` value for a terminal object and did not align with Mathlib's `TopCat.Presheaf.IsSheaf` API.
- Dependencies: `skyscraperPresheaf_eq_pushforward`, `TopCat.Presheaf.IsSheaf`, the one-point-space sheaf criterion from `Mathlib.Topology.Sheaves.PUnit`, and sheaf pushforward preservation from `Mathlib.Topology.Sheaves.Functors`.
- Formal statement review: under the chosen concrete-presheaf representation of `line-17`, the theorem states exactly that the constructed skyscraper presheaf at `p₀` with value `A` satisfies the sheaf condition.
- Source qualifiers:
  - Object class: skyscraper presheaf on a topological space with values in a category with a terminal object.
  - Quantifier order: `X`, `p₀`, `C`, terminal structure, `A`.
  - Parameter domain: any `TopCat` space and object `A` of any category with terminal object.
  - Output codomain: proposition asserting `Presheaf.IsSheaf`.
  - Equality/image condition: relies on the presheaf values from `line-17`.
  - Side conditions: categorical terminal object is available.
  - Follow-on claims: the proof identifies the skyscraper presheaf as a pushforward from the one-point space and uses that pushforwards preserve sheaves.
- Lean coverage: theorem target covers the sheaf-property claim for the Lean skyscraper presheaf constructed in `line-17`. The source pushforward argument is not part of the statement but is recorded as proof guidance.
- Scope changes: same representation change as `line-17`: the theorem is stated for the canonical constructed skyscraper presheaf rather than for an arbitrary presheaf satisfying a predicate. No additional mathematical assumptions are intended.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Consider the obvious continuous map `f : * → X` from the one-point space to `X` such that `f(*) = p₀`. Let `F` be a skyscraper presheaf on `X` at `p₀` with value `A`, and `G` a skyscraper presheaf on `*` with value `A`. Claim `F = f_* G`. For an open set `U ⊆ X`, if `p₀ ∈ U`, then `(f_*G)(U) = G(f⁻¹(U)) = G(*) = A`; if `p₀ ∉ U`, then `(f_*G)(U) = G(f⁻¹(U)) = G(∅) = 1_C`. Thus `F = f_*G`. On the one-point space, a presheaf is a sheaf iff its value at the empty set is terminal, so the skyscraper presheaf `G` is a sheaf on `*`. Since pushforward of a sheaf is a sheaf, `F = f_*G` is a sheaf on `X`.
- Prover notes: reproduce the source proof. Define/use the constant continuous map from `TopCat.of PUnit` to `X`, show the constructed skyscraper presheaf agrees with the pushforward of the one-point skyscraper presheaf by extensionality on opens, apply `Presheaf.isSheaf_on_punit_of_isTerminal` for the source sheaf on `PUnit`, then apply `Sheaf.pushforward_sheaf_of_sheaf` and transport the sheaf condition across the equality/isomorphism.

## Statement/Source Verification Gate

Independent review still needs to approve the representation choice, source-proof completeness, theorem statement fidelity, and Lean doc-comment prover notes. Do not start the prover queue until that review records approval.

Suggested next command after review approval:

```text
/prove ShadowBench/Source/Main.lean
```

## Formalization Rules

```text
open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

Formalize in Lean the following named items from Text.

1. Definition (skyscraperPresheaf_eq_pushforward)
   The definition must be named `skyscraperPresheaf_eq_pushforward`.
2. Theorem (skyscraperPresheaf_isSheaf)
   The theorem must be named `skyscraperPresheaf_isSheaf`.

Every listed named item must be formalized with exactly the stated Lean name.
```
