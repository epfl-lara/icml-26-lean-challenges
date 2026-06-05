# Formalization Blueprint: `topology/L3/top_gen_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Document Inspection

- `formalization_document_inspect docs/source.tex` succeeded; extraction status `ok`.
- Preflight detected one theorem-like block and no sections, labels, references, citations, bibliography files, PDFs, or figures.

## Detected Theorem-Like Blocks

1. `line-17` (theorem, lines 17-20) - isProperMap_proj_iff_compactSpace

## Source Map

- line-17 -> `isProperMap_proj_iff_compactSpace` (`docs/source.tex` lines 17-20; proof lines 22-72)

## Source inventory

- label: line-17
  source_id: line-17
  kind: theorem
  source_title: isProperMap_proj_iff_compactSpace
  planned_lean_declaration: isProperMap_proj_iff_compactSpace
  source_locator: docs/source.tex lines 17-20, proof lines 22-72
  Source qualifiers: mathematical object class is a topological fiber bundle projection `π : E → M` with typical fiber `F`; quantifier order is base, typical fiber, then bundle/projection; parameter domain is the bundle total space; output codomain is `M`; equality/image conditions are not part of the theorem statement; statement-level side conditions are not explicit in the source, though the proof chooses a base point; conclusion is properness of the projection iff compactness of `F`; no follow-on conclusion beyond the iff.
  Lean coverage: theorem `isProperMap_proj_iff_compactSpace` states `IsProperMap (Bundle.TotalSpace.proj (F := F) (E := E)) ↔ CompactSpace F` for Mathlib bundles `[FiberBundle F E]` over a nonempty base; this is full coverage for the recorded Mathlib-canonical, nonempty-base translation and partial literal coverage of an arbitrary-map notation because no separate arbitrary-projection bridge declaration is introduced.
  Scope changes: representation change from the source's arbitrary-looking projection notation to Mathlib's canonical `Bundle.TotalSpace.proj`; added side condition `[Nonempty M]`; Mathlib predicate `IsProperMap` used for proper maps; no statement-level equality/image condition or follow-on claim is omitted.
  Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source theorem skeleton `isProperMap_proj_iff_compactSpace`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so plain project builds cover the generated target module.

## Import Plan

```lean
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Proper.Basic
```

The first two imports come from `docs/instructions.md`. `Mathlib.Topology.Maps.Proper.Basic` is added because the source theorem is about proper maps, formalized in Mathlib as `IsProperMap`.

## Suggested Search Modules

- `Mathlib.Topology.FiberBundle.Basic`: `FiberBundle`, `FiberBundle.continuous_proj`, `FiberBundle.trivializationAt`, fiber embeddings.
- `Mathlib.Topology.Maps.Proper.Basic`: `IsProperMap`, `isProperMap_iff_isClosedMap_and_compact_fibers`, `IsProperMap.isCompact_preimage`, `isProperMap_fst_of_compactSpace`.
- `Mathlib.Topology.FiberBundle.Constructions`: possible helper facts for trivial bundles/products if the proof run needs comparison with the product projection.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`.
- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` all propose the required name and the high-level shape `proper projection ↔ CompactSpace F`, but use the non-Mathlib identifier `ProperMap` and an invalid arbitrary-map form `FiberBundle π`.
- `docs/skeletons/Skeleton4.lean` has the same proposed shape and additionally contains a malformed duplicate `:= by sorry`.
- Adopted from skeletons: declaration name `isProperMap_proj_iff_compactSpace` and the target equivalence with `CompactSpace F`.
- Corrected from skeletons: use Mathlib's `IsProperMap` and Mathlib's dependent bundle representation `FiberBundle F E` on the canonical projection `Bundle.TotalSpace.proj`.

## Source Statement Inventory

### line-17

- Planned Lean declaration: `isProperMap_proj_iff_compactSpace`
- Source inventory entry: `line-17`
- Source theorem-like block: `line-17`
- Source locator: `docs/source.tex` lines 17--20 (`line-17`); proof lines 22--72.
- Source statement text:
  ```text
  Suppose π : E → M is a fiber bundle with fiber F. Then π is a proper map if and only if F is compact.
  ```
- Skeleton candidate used: Skeletons 1-3 for the name and intended equivalence only; Skeleton4 rejected as malformed. All skeleton statements were corrected to match Mathlib naming and representation.
- Dependencies:
  - Mathlib object-class bridge: `FiberBundle F E` represents a topological fiber bundle with typical fiber `F` over base `M`; the total space is `Bundle.TotalSpace F E` and the projection is `Bundle.TotalSpace.proj (F := F) (E := E)`.
  - Proper-map definition: `IsProperMap` from `Mathlib.Topology.Maps.Proper.Basic`.
  - Compactness predicate: `CompactSpace F`.
  - Expected proof ingredients: `FiberBundle.continuous_proj`, local trivializations `FiberBundle.trivializationAt`, compact fibers via homeomorphism to `F`, `IsProperMap.isCompact_preimage`, `isProperMap_iff_isClosedMap_and_compact_fibers`, and the proper/closed projection theorem `isProperMap_fst_of_compactSpace` for products.
- Formal statement review:
  - Reviewed against source statement lines 17--20 and complete proof lines 22--72.
  - Source quantifies over a fiber bundle projection `π : E → M` with typical fiber `F`.
  - Lean uses Mathlib's canonical representation of such a projection: for a dependent fiber family `E : M → Type*`, the total space is `Bundle.TotalSpace F E` and the projection is `Bundle.TotalSpace.proj`.
  - The theorem states `IsProperMap (Bundle.TotalSpace.proj (F := F) (E := E)) ↔ CompactSpace F`, preserving the source equivalence between properness of the projection and compactness of the typical fiber under the recorded nonempty-base restriction.
- Source qualifiers:
  - Mathematical object class: topological fiber bundle projection with typical fiber `F`.
  - Quantifier order: arbitrary base type `M`, typical fiber type `F`, then a bundle over `M`; Lean represents this as a dependent fiber family `E : M → Type*` with `[FiberBundle F E]`.
  - Parameter domain: the map domain is the total space of the bundle; Lean domain is `Bundle.TotalSpace F E`.
  - Output codomain: the projection lands in the base `M`; Lean codomain is `M`.
  - Equality/image condition: no separate equality or image condition is part of the source theorem statement. The local trivialization equation and image identities occur in the proof and are recorded as proof ingredients.
  - Properness condition: properness of the bundle projection `π`; Lean uses `IsProperMap (Bundle.TotalSpace.proj (F := F) (E := E))`.
  - Compactness condition: compactness of the typical fiber `F`; Lean uses `CompactSpace F`.
  - Side conditions: the source statement does not explicitly require `M` to be nonempty, but the source proof chooses a base point `p ∈ M`; Lean adds `[Nonempty M]` because the unqualified equivalence is false over an empty base with arbitrary typical fiber.
  - Follow-on claims: no additional conclusion beyond the iff is stated in the source theorem.
- Lean coverage:
  - Full coverage for the recorded nonempty-base, Mathlib-canonical representation of the source theorem: `{M F : Type*} [TopologicalSpace M] [TopologicalSpace F] [Nonempty M] (E : M → Type*) [TopologicalSpace (Bundle.TotalSpace F E)] [∀ m, TopologicalSpace (E m)] [FiberBundle F E]`.
  - The source projection domain and codomain are covered by `Bundle.TotalSpace.proj (F := F) (E := E) : Bundle.TotalSpace F E → M`.
  - The source iff is covered by `IsProperMap (Bundle.TotalSpace.proj (F := F) (E := E)) ↔ CompactSpace F`.
  - Literal arbitrary-map notation `π : E → M` has partial coverage only: this draft does not add a separate arbitrary-projection bridge theorem, and instead records the intentional Mathlib representation change below.
- Scope changes: representation change from the source's arbitrary-looking projection notation to Mathlib's canonical `Bundle.TotalSpace.proj`; added side condition `[Nonempty M]`; Mathlib predicate `IsProperMap` used for proper maps; no statement-level equality/image condition or follow-on claim is omitted.
  - Representation bridge detail: an arbitrary-looking source projection `π : E → M` is represented by Mathlib's canonical total-space projection `Bundle.TotalSpace.proj` under `[FiberBundle F E]`.
  - Nonempty-base detail: `[Nonempty M]` makes the reverse implication from properness to compactness faithful to the source proof and mathematically valid.
  - Naming detail: the Lean statement uses `IsProperMap` rather than the skeletons' nonexisting `ProperMap`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
Because π : E → M is a fiber bundle projection, it is continuous, and for every p ∈ M there exists an open neighborhood U of p and a homeomorphism
Φ : π^{-1}(U) → U × F
such that
π|_{π^{-1}(U)} = pr₁ ∘ Φ,
where pr₁ : U × F → U is projection onto the first factor.

(⇒) Suppose π is proper. For any p ∈ M, the singleton {p} is compact. Hence π^{-1}({p}) = π^{-1}(p) is compact. But each fiber π^{-1}(p) is homeomorphic to F, so F is compact.

(⇐) Suppose F is compact. We will show that π is proper by proving that π is a continuous closed map with compact fibers (Proposition A.53(b)). First, for each p ∈ M, the fiber π^{-1}(p) is homeomorphic to F, hence compact.

Now let C ⊆ E be closed. We show that π(C) is closed in M. Let p ∈ M \ π(C). Choose a trivializing neighborhood U of p and a trivialization Φ : π^{-1}(U) → U × F. Then C ∩ π^{-1}(U) is closed in π^{-1}(U), so Φ(C ∩ π^{-1}(U)) is closed in U × F. Since F is compact, the projection pr₁ : U × F → U is a closed map. Therefore
π(C) ∩ U = π(C ∩ π^{-1}(U)) = pr₁(Φ(C ∩ π^{-1}(U)))
is closed in U.

Because p ∉ π(C), we have p ∈ U \ (π(C) ∩ U), and this is an open neighborhood of p in M disjoint from π(C). Hence every point of M \ π(C) has an open neighborhood contained in M \ π(C), so M \ π(C) is open. Thus π(C) is closed, and π is a closed map.

Therefore π is a continuous closed map with compact fibers. By Proposition A.53(b), π is proper. Hence π is proper if and only if F is compact.
```

- Prover notes:
  - For `→`, choose a base point from `[Nonempty M]`; apply `IsProperMap.isCompact_preimage` to the compact singleton in `M`, identify the preimage with the fiber over that point, and use the fiber/trivialization homeomorphism with `F`.
  - For `←`, use `isProperMap_iff_isClosedMap_and_compact_fibers`. Continuity is `FiberBundle.continuous_proj`. Compact fibers follow from the local/fiber homeomorphism to `F`. Closedness should be proved locally with `FiberBundle.trivializationAt`: under a trivialization, the image of a closed set over a trivializing open set is the first projection of a closed subset of `U × F`, closed because `F` is compact.
  - If a direct Mathlib theorem for compact-fiber bundle projections is available, it should replace the local closed-map argument.

## Formalization Checklist

- [x] Source document inspected with deterministic document inspection.
- [x] Companion instructions and skeletons read.
- [x] Mathlib/local search performed before drafting.
- [x] Source inventory entry `line-17` recorded.
- [x] Lean declaration skeleton drafted with source-aware proof notes.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
