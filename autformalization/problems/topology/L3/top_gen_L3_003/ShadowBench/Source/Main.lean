import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Proper.Basic

open TopologicalSpace

/--
Source theorem `line-17` from `docs/source.tex`: if `π : E → M` is a fiber bundle
projection with typical fiber `F`, then `π` is proper iff `F` is compact.

Source proof: properness implies compactness by choosing a base point, applying properness to
the compact singleton in the base, and using the homeomorphism between that fiber and `F`.
Conversely, if `F` is compact, the projection is continuous, all fibers are compact, and local
trivializations reduce closedness of the projection to closedness of `pr₁ : U × F → U`.
Then the closed-map/compact-fiber criterion for proper maps gives properness.

Prover notes: Mathlib represents this source fiber-bundle projection as the canonical projection
`Bundle.TotalSpace.proj (F := F) (E := E)` under `[FiberBundle F E]`. The nonempty-base
hypothesis records the source proof's choice of a base point; without it the iff can fail over an
empty base. Useful facts include `FiberBundle.continuous_proj`, `FiberBundle.trivializationAt`,
`IsProperMap.isCompact_preimage`, `isProperMap_iff_isClosedMap_and_compact_fibers`, and
`isProperMap_fst_of_compactSpace`.
-/
theorem isProperMap_proj_iff_compactSpace
    {M F : Type*} [TopologicalSpace M] [TopologicalSpace F] [Nonempty M]
    (E : M → Type*) [TopologicalSpace (Bundle.TotalSpace F E)]
    [∀ m : M, TopologicalSpace (E m)] [FiberBundle F E] :
    IsProperMap (Bundle.TotalSpace.proj (F := F) (E := E)) ↔ CompactSpace F := by
  sorry
