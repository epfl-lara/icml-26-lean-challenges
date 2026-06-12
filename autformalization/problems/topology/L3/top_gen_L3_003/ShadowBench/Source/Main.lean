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
  constructor
  · intro hprop
    classical
    obtain ⟨m⟩ := ‹Nonempty M›
    have hpre : IsCompact ((Bundle.TotalSpace.proj (F := F) (E := E)) ⁻¹' ({m} : Set M)) :=
      hprop.isCompact_preimage isCompact_singleton
    have hE : CompactSpace (E m) := by
      refine ⟨?_⟩
      rw [(FiberBundle.totalSpaceMk_isEmbedding F E m).isCompact_iff]
      simpa [Bundle.TotalSpace.range_mk, Set.image_univ] using hpre
    haveI : CompactSpace (E m) := hE
    exact (FiberBundle.homeomorphAt F E m).compactSpace
  · intro hF
    classical
    haveI : CompactSpace F := hF
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨FiberBundle.continuous_proj F E, ?_, ?_⟩
    · let V : M → Set M := fun m => (FiberBundle.trivializationAt F E m).baseSet
      let hopen : ∀ m : M, IsOpen (V m) := fun m =>
        (FiberBundle.trivializationAt F E m).open_baseSet
      let U : M → Opens M := fun m => ⟨V m, hopen m⟩
      have hU : TopologicalSpace.IsOpenCover U := by
        refine TopologicalSpace.IsOpenCover.mk ?_
        ext x
        simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe, Opens.coe_top,
          Set.mem_univ, iff_true]
        exact ⟨x, FiberBundle.mem_baseSet_trivializationAt F E x⟩
      rw [hU.isClosedMap_iff_restrictPreimage]
      intro m
      dsimp [U, V, hopen]
      let e : Bundle.Trivialization F (Bundle.TotalSpace.proj (F := F) (E := E)) :=
        FiberBundle.trivializationAt F E m
      change IsClosedMap (e.baseSet.restrictPreimage (Bundle.TotalSpace.proj (F := F) (E := E)))
      have hproper :
          IsProperMap ((Prod.fst : e.baseSet × F → e.baseSet) ∘
            (e.preimageHomeomorph (s := e.baseSet) (by intro x hx; exact hx))) := by
        exact isProperMap_fst_of_compactSpace.comp
          (e.preimageHomeomorph (s := e.baseSet) (by intro x hx; exact hx)).isProperMap
      have hproper' :
          IsProperMap (e.baseSet.restrictPreimage (Bundle.TotalSpace.proj (F := F) (E := E))) := by
        convert hproper using 1
        ext p
        simp [Set.restrictPreimage]
      exact hproper'.isClosedMap
    · intro m
      haveI : CompactSpace (E m) := (FiberBundle.homeomorphAt F E m).symm.compactSpace
      have hpre : IsCompact (Set.range ((↑) : E m → Bundle.TotalSpace F E)) := by
        simpa [Set.image_univ] using
          (isCompact_univ.image (FiberBundle.continuous_totalSpaceMk F E m))
      simpa [Bundle.TotalSpace.range_mk] using hpre
