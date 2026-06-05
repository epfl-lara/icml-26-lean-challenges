# Formalization Blueprint: `topology/L2/top_gen_L2_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed declaration `monodromy_theorem`.
- `ShadowBench/Source.lean`: root project module importing `ShadowBench.Source.Main`, so the generated file is covered by project verification.

## Import Plan

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.UnitInterval
```

## Suggested Search Modules

These are proof-search hints for the later prover and are not direct imports of the current draft unless proof repair shows they are needed.

- `Mathlib.Topology.Homotopy.Lifting`: contains covering-map path/homotopy lifting and uniqueness lemmas such as `IsCoveringMap.liftHomotopy`, `IsCoveringMap.liftPath`, and `IsCoveringMap.existsUnique_continuousMap_lifts`.
- `Mathlib.Topology.ContinuousMap.Defs`: background for `C(I, E)` / `ContinuousMap` notation, already available through current imports.

## Required Names

- `monodromy_theorem`

## Detected Theorem-Like Blocks

1. `line-18` (theorem, lines 18-27) - monodromy_theorem

## Source Map

- line-18 -> `monodromy_theorem` (`docs/source.tex` lines 18-27; proof lines 27-40)

## Source inventory

- label: line-18
  source_id: line-18
  kind: theorem
  source_title: monodromy_theorem
  planned_lean_declaration: monodromy_theorem
  source_locator: docs/source.tex lines 18-27, proof lines 27-40
  details: Full statement-fidelity details and prover notes are in the matching statement inventory entry below.

## Source Statement Inventory

### line-18

- Source inventory entry `line-18`: theorem `[monodromy_theorem]` in `docs/source.tex`.
- Source label: `line-18`
- Source inventory entry: `line-18`
- Source inventory label: `line-18`
- Source block label: `line-18`
- Preflight label: `line-18`
- Planned Lean declarations: `monodromy_theorem`
- Source locator: `docs/source.tex`, theorem lines 18-27; proof lines 27-40.
- Source statement:
  Let `γ₀, γ₁ : I → X` be paths and let `γ : I × I → X` be a homotopy rel. endpoints between them. Let `Γ : I → C(I, E)` be a family of continuous paths in `E` such that `p(Γ(t)(s)) = γ(t,s)` for all `t,s ∈ I`, and `Γ(t)(0) = Γ(0)(0)` for all `t ∈ I`. Then `Γ(t)(1) = Γ(0)(1)` for all `t ∈ I`.
- Adopted statement shape:
  ```lean
  theorem monodromy_theorem {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
      (p : E → X) (hp : IsCoveringMap p)
      {x y : X}
      (γ₀ γ₁ : Path x y)
      (γ : Path.Homotopy γ₀ γ₁)
      (Γ : I → C(I, E))
      (hΓ : ∀ t s, p (Γ t s) = γ (t, s))
      (hΓ₀ : ∀ t, Γ t 0 = Γ 0 0) :
      ∀ t, Γ t 1 = Γ 0 1 := by sorry
  ```
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean` shaped the final statement because it represents source paths as `Path x y`, the homotopy rel. endpoints as `Path.Homotopy γ₀ γ₁`, and the family of continuous paths as `Γ : I → C(I, E)`. The skeleton binder `[IsCoveringMap p]` was corrected to the term hypothesis `(hp : IsCoveringMap p)`, because `IsCoveringMap` is not a typeclass in this Mathlib version. Skeletons 1-3 were not adopted because they use raw functions plus endpoint equations and omit the structured `C(I,E)` path-family representation from the source.
- Dependencies:
  - `Topology.unitInterval` / notation `I` for the source interval.
  - `Path x y` and `Path.Homotopy γ₀ γ₁` from `Mathlib.Topology.Homotopy.Path` for paths and homotopies rel. endpoints.
  - `C(I, E)` / `ContinuousMap I E` for the continuous path family.
  - `IsCoveringMap p` from `Mathlib.Topology.Covering.Basic` to expose the separated/unique-lifting hypothesis used in the source proof.
- Formal statement review:
  - `γ₀, γ₁ : Path x y` records the source paths with common endpoints.
  - `γ : Path.Homotopy γ₀ γ₁` records a homotopy rel. endpoints; Mathlib's structure includes endpoint constraints such as constancy on `s = 0` and `s = 1`.
  - `Γ : I → C(I, E)` preserves the source codomain `C(I,E)` rather than reducing to arbitrary functions with continuity hypotheses.
  - `hΓ : ∀ t s, p (Γ t s) = γ (t, s)` and `hΓ₀ : ∀ t, Γ t 0 = Γ 0 0` preserve the two displayed source hypotheses with quantifier order `t` then `s`.
  - Conclusion `∀ t, Γ t 1 = Γ 0 1` matches the source endpoint conclusion.
- Source qualifiers:
  - Mathematical object class: topological spaces `X` and `E`, interval `I = [0,1]`, paths in `X`, homotopy rel. endpoints, continuous paths in `E`, and a projection map `p : E → X` with separated/unique-lifting behavior invoked in the proof.
  - Quantifier order: topological spaces and `p`; common endpoints `x y`; source paths `γ₀ γ₁`; homotopy `γ`; lifted path family `Γ`; displayed hypotheses `hΓ` and `hΓ₀`; conclusion for all `t : I`.
  - Parameter domain/codomain: `γ₀ γ₁ : I → X` via `Path x y`; `γ : I × I → X` via `Path.Homotopy`; `Γ : I → C(I,E)`; `p : E → X`.
  - Equality/image conditions: `p (Γ t s) = γ (t,s)` for all `t s`; `Γ t 0 = Γ 0 0` for all `t`; conclusion `Γ t 1 = Γ 0 1` for all `t`.
  - Side conditions: homotopy rel. endpoints encoded in `Path.Homotopy`; proof's separated/unique-lifting condition represented by `hp : IsCoveringMap p`.
  - Follow-on claims: none beyond endpoint constancy of `Γ`.
- Lean coverage:
  - Source paths and endpoint equality: covered by `γ₀ γ₁ : Path x y`.
  - Source homotopy rel. endpoints: covered by `γ : Path.Homotopy γ₀ γ₁`.
  - Source family of continuous paths: covered by `Γ : I → C(I,E)`.
  - Projection equality and common initial point: covered exactly by `hΓ` and `hΓ₀`.
  - Endpoint conclusion: covered exactly by `∀ t, Γ t 1 = Γ 0 1`.
  - Proof's separated/unique-lifting premise: represented by the explicit covering-map hypothesis `hp : IsCoveringMap p`.
- Scope changes:
  - The isolated source theorem statement does not list a type or hypothesis for `p`, but its proof explicitly says “Since `p` is separated” and uses uniqueness of lifts. The Lean draft makes this implicit ambient assumption explicit as `(hp : IsCoveringMap p)`. This is a stronger standard covering-map assumption than the proof phrase “separated” alone; independent source/statement review should confirm that the surrounding intended context is a covering map before treating coverage as exact.
  - The Lean draft uses Mathlib's structured `Path x y` and `Path.Homotopy` instead of raw functions plus separate continuity/endpoint fields. This is a representation change that is intended to preserve the source object class and endpoint-relativity.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  Define `G : I × I → E` by `G(s,t) = Γ(t)(s)`. Then for each fixed `t`, the map `s ↦ G(s,t)` is continuous, and by hypothesis the map `t ↦ G(0,t)` is constant, hence continuous. Moreover `p(G(s,t)) = p(Γ(t)(s)) = γ(t,s) = (γ ∘ swap)(s,t)`. By Theorem B, `G` is continuous. Now consider the path `t ↦ G(1,t)` in `E`. Its projection is `t ↦ p(G(1,t)) = γ(t,1)`, which is constant in `t` because `γ` is a homotopy rel. endpoints. Since `p` is separated and `G(0,t)` is constant, uniqueness of lifts forces `G(1,t)` to be constant. Thus `G(1,t)=G(1,0)` for all `t`, i.e. `Γ(t)(1)=Γ(0)(1)`.
- Prover notes:
  The later prover should mimic the source proof. Repackage `Γ` as the two-variable map `G(s,t) = Γ t s`; use `hΓ` and `Path.Homotopy.target` to show the projected endpoint path `t ↦ p (Γ t 1)` is constant. Then use covering-map uniqueness/lifting tools, likely from `Mathlib.Topology.Homotopy.Lifting`, to compare the endpoint path `t ↦ Γ t 1` with the constant lift at `Γ 0 1`. The common-start hypothesis `hΓ₀` supplies the lift normalization required for uniqueness.

## Formalization Rules From Instructions

```text
open Topology unitInterval

The theorem must be named `monodromy_theorem`.
Matched source text: theorem `[monodromy_theorem]` in `docs/source.tex` lines 18-27.
```
