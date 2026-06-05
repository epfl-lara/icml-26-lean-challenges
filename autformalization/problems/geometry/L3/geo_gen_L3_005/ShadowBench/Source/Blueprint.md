# Formalization Blueprint: `geometry/L3/geo_gen_L3_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Draft status: source inventory and Lean statement accepted by formalization PASS and 2026-06-05 audit; ready for later prove workflow.

## Source Statement Inventory

- `line-17`: mapped to Lean declaration `proj_homotopyEquiv`.

### line-17

Source inventory entry: `line-17`.

#### Theorem `proj_homotopyEquiv`

- Source inventory id: `line-17`
- Source locator: `docs/source.tex`, theorem environment lines 17-20; proof block lines 22-53.
- Source statement: Let `E` be a vector bundle over a topological space `M`. Show that the projection map `π : E → M` is a homotopy equivalence.
- Planned Lean declarations: `proj_homotopyEquiv` in `ShadowBench/Source/Main.lean`.
- Lean statement shape: for a Mathlib real topological vector bundle represented by a dependent fiber family `E : M → Type*` with model fiber `F`, the continuous projection `π F E : Bundle.TotalSpace F E → M` is the forward map of some `ContinuousMap.HomotopyEquiv (Bundle.TotalSpace F E) M`.
- Dependencies: `Mathlib.Topology.Homotopy.Equiv`, `Mathlib.Topology.VectorBundle.Basic`; uses `Bundle.TotalSpace`, notation/definition `π F E`, `FiberBundle.continuous_proj`, `Bundle.zeroSection`, `Bundle.zeroSection_proj`, `Bundle.Trivialization.continuous_zeroSection`, and the `ContinuousMap.HomotopyEquiv` structure.
- Skeleton candidate used: Skeletons 1, 2, and 3 propose the required name but use the non-existent or wrong shape `[VectorBundle M E]`, `Bundle.proj M E`, and `IsHomotopyEquiv`. Skeleton 4 additionally has malformed duplicate proof syntax. The final statement keeps the required name but replaces the candidate type by Mathlib's actual vector-bundle representation.
- Formal statement review: the source says the projection map itself is a homotopy equivalence. A bare conclusion `Bundle.TotalSpace F E ≃ₕ M` would only assert existence of some homotopy equivalence, so the planned Lean statement explicitly quantifies a homotopy equivalence whose `toFun` is the continuous bundle projection.
- Source qualifiers:
  - Mathematical object class: vector bundle over a topological base space `M`.
  - Quantifier order: first choose the base/topological space, then choose a vector bundle over it; the Lean statement represents this by choosing `M`, a model fiber `F`, and fiber family `E : M → Type*`, then assuming the topology, fiber-bundle, and vector-bundle instances.
  - Parameter domain: the total space of the vector bundle, denoted `E` in the source and represented in Mathlib as `Bundle.TotalSpace F E`.
  - Output codomain: the base space `M`.
  - Equality/image condition: the map whose homotopy-equivalence status is asserted is the bundle projection `π : E → M`; in Lean the forward continuous map of the homotopy equivalence must be exactly `π F E` equipped with `FiberBundle.continuous_proj`.
  - Side conditions: the proof uses scalar multiplication by `t ∈ [0,1]`, so the Lean statement specializes the otherwise implicit vector-bundle scalar field to real scalars and requires a real normed model vector space with real module fibers.
  - Follow-on claims in the source statement: none beyond the projection being a homotopy equivalence. The zero section and fiberwise scaling homotopy occur in the source proof and are recorded below as proof-witness/prover notes rather than as additional theorem clauses.
- Lean coverage:
  - `VectorBundle ℝ F E` plus `FiberBundle F E` cover the vector-bundle object class in Mathlib's representation.
  - `Bundle.TotalSpace F E` covers the total space called `E` in the source.
  - `π F E` covers the projection `π : E → M`.
  - `∃ h : ContinuousMap.HomotopyEquiv (Bundle.TotalSpace F E) M, h.toFun = ...` covers the assertion that this exact projection map is a homotopy equivalence, rather than merely asserting an unrelated homotopy equivalence between total space and base.
  - The real scalar field assumptions cover the proof's interval homotopy `H(v,t)=t • v`.
- Scope changes: representation bridge from the source's single total-space symbol `E` to Mathlib's dependent bundle data `E : M → Type*` and total-space type `Bundle.TotalSpace F E`; scalar field made explicit as `ℝ` to match the interval-scaling proof. This is full coverage under Mathlib's vector-bundle representation, not a theorem weakening.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Let `σ : M → E` be the zero section, defined by `σ(p)=0_p ∈ E_p`. Then `π ∘ σ = id_M`, because the zero vector `0_p` lies in the fiber `E_p`. It remains to show that `σ ∘ π` is homotopic to `id_E`. Define `H : E × [0,1] → E` by `H(v,t)=t v`, where `v ∈ E_p` for some `p ∈ M`, and `t v` denotes scalar multiplication in the fiber `E_p`. Moreover, `H` is continuous since scalar multiplication is continuous in each local trivialization of the vector bundle. At the endpoints, `H(v,1)=v`, so `H_1=id_E`, and `H(v,0)=0_p=σ(π(v))`, so `H_0=σ∘π`. Thus `H` is a homotopy from `σ∘π` to `id_E`; therefore `π` has homotopy inverse `σ` and is a homotopy equivalence.
- Prover notes: build a `ContinuousMap.HomotopyEquiv` with `toFun` the projection and `invFun` the zero section. The left inverse on the base is pointwise `Bundle.zeroSection_proj`. The right homotopy should be the fiberwise scaling homotopy from `0 • v` to `1 • v`; use local trivializations to prove continuity or locate an existing Mathlib lemma about fiberwise scalar multiplication/homotopies in vector bundles.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: generated formalization for the single source theorem `line-17`.
- `ShadowBench/Source.lean`: root submodule aggregator, currently imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: project root module, currently imports `ShadowBench.Source`, so plain project builds include the generated target file.

## Import Plan

```lean
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.VectorBundle.Basic
```

## Suggested Search Modules

- `Mathlib.Topology.Homotopy.Basic` for the `ContinuousMap.Homotopy` API and interval homotopies.
- `Mathlib.Topology.VectorBundle.Basic` for zero sections, projection continuity, and vector-bundle local trivialization lemmas.
- `Mathlib.Topology.FiberBundle.Basic` for `FiberBundle.continuous_proj` and total-space topology facts.

## Required Names

- `proj_homotopyEquiv`

## Formalization Rules

```text
open Bundle ContinuousMap Topology

/-
Formalize in Lean the Theorem (proj_homotopyEquiv) from Text.

The Lean declaration must be named exactly:
- `proj_homotopyEquiv`
   Matched text (candidate 0, theorem, label=proj_homotopyEquiv): \begin{theorem}[proj_homotopyEquiv] Let $E$ be a vector bundle over a topological space $M$.
                                                                  Show that the projection map $\pi : E \to M$ is a homotopy equivalence. \end{theorem}
-/
```

## Review Checklist

- [ ] Source document inspection recorded for reviewer.
- [ ] Candidate skeleton comparison checked by reviewer.
- [ ] Blueprint source inventory entry `line-17` checked by reviewer.
- [ ] Lean statement and doc-comment prover notes checked by reviewer.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
