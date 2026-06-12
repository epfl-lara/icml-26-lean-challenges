import Mathlib

open CategoryTheory Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/--
A topological space is locally noetherian in the sense used by the source theorem: every point
has an open neighbourhood whose subspace topology is noetherian.
-/
def TopologicallyLocallyNoetherian (α : Type u) [TopologicalSpace α] : Prop :=
  ∀ x : α, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ NoetherianSpace U

/--
Property (P) from the source for a fixed affine open `W` of the target: the open preimage is a
finite union of affine opens `U` of `X`, and each induced map on rings of sections
`Γ(W, 𝒪_Y) ⟶ Γ(U, 𝒪_X)` is of finite type.
-/
def HasPropertyP {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    (_hW : IsAffineOpen W) : Prop :=
  ∃ s : Set X.affineOpens,
    s.Finite ∧
      (f ⁻¹ᵁ W = ⨆ U ∈ s, (U : X.Opens)) ∧
        ∀ U : X.affineOpens, U ∈ s →
          ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ W,
            (f.appLE W (U : X.Opens) e).hom.FiniteType

/--
Source definition `FiniteType` (lines 17--28): a morphism of schemes is of finite type if the
target is covered by affine opens satisfying property (P).
-/
def FiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (V : ι → Y.affineOpens),
    (⨆ i, (V i : Y.Opens)) = ⊤ ∧
      ∀ i, HasPropertyP f (V i : Y.Opens) (V i).2

/--
Source proof: let `W` be affine, cover it by finitely many distinguished opens lying inside the
affine opens from the finite-type definition, then refine the finite affine covers of their
preimages by basic opens. Localization preserves finite type, so the induced section maps over
these refined basic opens remain finite type; the finite refinements assemble to property (P) for
`W`.

Prover notes: unfold `FiniteType` and `HasPropertyP`; use compactness of affine opens, basic-open
refinements inside affine schemes, and `RingHom.FiniteType` stability under localization.
-/
theorem hasPropertyP_of_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : FiniteType f)
    (W : Y.Opens) (hW : IsAffineOpen W) : HasPropertyP f W hW := by
  rcases hf with ⟨ι, V, hcover, hPV⟩
  have hqc : QuasiCompact f := by
    refine AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top
      (P := @QuasiCompact) (Q := fun X _ _ _ => CompactSpace X) V hcover ?_
    intro i
    rcases hPV i with ⟨s, hfin, hcov, hft⟩
    have hcomp : IsCompact (↑(f ⁻¹ᵁ (V i : Y.Opens)) : Set X) :=
      AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ⟨s, hfin, hcov⟩
    exact isCompact_iff_compactSpace.mp hcomp
  have hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource @RingHom.FiniteType := by
    exact (RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_stableUnderComposition RingHom.finiteType_holdsForLocalizationAway).1
  have hlf : LocallyOfFiniteType f := by
    rw [AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) (Q := @RingHom.FiniteType) hQ]
    intro x
    have hy : f.base x ∈ (⨆ i, (V i : Y.Opens)) := by
      rw [hcover]
      simp
    rcases (TopologicalSpace.Opens.mem_iSup.mp hy) with ⟨i, hi⟩
    rcases hPV i with ⟨s, hfin, hcov, hft⟩
    have hxpre : x ∈ (f ⁻¹ᵁ (V i : Y.Opens)) := by
      simpa using hi
    have hxcover : x ∈ (⨆ U ∈ s, (U : X.Opens)) := by
      simpa [hcov] using hxpre
    rcases (TopologicalSpace.Opens.mem_iSup.mp hxcover) with ⟨U, hxU'⟩
    rcases (TopologicalSpace.Opens.mem_iSup.mp hxU') with ⟨hUs, hxU⟩
    rcases hft U hUs with ⟨e, hfinite⟩
    exact ⟨V i, U, hxU, e, hfinite⟩
  have hcompW : IsCompact (↑(f ⁻¹ᵁ W) : Set X) := by
    exact (AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen.mp hqc) W hW
  rcases AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hcompW with ⟨s, hfin, hcov⟩
  refine ⟨s, hfin, hcov, ?_⟩
  intro U hUs
  have e : (U : X.Opens) ≤ f ⁻¹ᵁ W := by
    rw [hcov]
    exact le_iSup_of_le U (le_iSup_of_le hUs le_rfl)
  refine ⟨e, ?_⟩
  haveI : LocallyOfFiniteType f := hlf
  exact AlgebraicGeometry.Scheme.Hom.finiteType_appLE f hW U.2 e

/--
Source proof: reduce to affine targets. For an immersion, the image is locally closed. Under the
locally-noetherian target alternative, work on noetherian affine neighbourhoods; under the
noetherian-domain alternative, use noetherian compactness of the underlying space of `X`. In both
cases obtain a finite affine cover of the source by intersections with basic opens of the affine
target. These intersections are closed in basic opens, so their coordinate rings are quotients of
localizations of the target coordinate ring, hence finite type. This gives the source finite-type
cover condition.

Prover notes: combine the source proof with Mathlib facts about `IsImmersion`, noetherian spaces,
finite affine covers of compact opens, closed immersions into affine schemes, localization, and
quotient maps being `RingHom.FiniteType`.
-/
private lemma noetherianSpace_of_subset' {α : Type*} [TopologicalSpace α]
    {V W : Set α} (hW : TopologicalSpace.NoetherianSpace W) (hVW : V ⊆ W) :
    TopologicalSpace.NoetherianSpace V := by
  rw [TopologicalSpace.noetherianSpace_set_iff] at hW ⊢
  intro t ht
  exact hW t (fun x hx => hVW (ht hx))

private lemma isCompact_preimage_of_noetherian_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] (W : Y.Opens) (hWnoeth : TopologicalSpace.NoetherianSpace (W : Set Y)) :
    IsCompact (↑((TopologicalSpace.Opens.map f.base).obj W) : Set X) := by
  have himg : IsCompact (f '' (↑((TopologicalSpace.Opens.map f.base).obj W) : Set X)) := by
    rw [TopologicalSpace.noetherianSpace_set_iff] at hWnoeth
    apply hWnoeth
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hx
  exact (IsPreimmersion.isEmbedding f).isCompact_iff.mpr himg

private lemma hasPropertyP_of_isCompact_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (W : Y.Opens) (hW : IsAffineOpen W)
    (hcompact : IsCompact (↑((TopologicalSpace.Opens.map f.base).obj W) : Set X)) :
    HasPropertyP f W hW := by
  obtain ⟨s, hsfin, hcover_set⟩ :=
    AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨hcompact, ((TopologicalSpace.Opens.map f.base).obj W).2⟩
  have hcover_open : (TopologicalSpace.Opens.map f.base).obj W = ⨆ U ∈ s, (U : X.Opens) := by
    apply TopologicalSpace.Opens.ext
    simp [hcover_set]
  refine ⟨s, hsfin, hcover_open, ?_⟩
  intro U hU
  have hle : (U : X.Opens) ≤ (TopologicalSpace.Opens.map f.base).obj W := by
    rw [hcover_open]
    exact le_iSup_of_le U (le_iSup_of_le hU le_rfl)
  exact ⟨hle, Scheme.Hom.finiteType_appLE f hW U.property hle⟩

private theorem finiteType_of_quasiCompact_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFiniteType f] : FiniteType f := by
  refine ⟨Y.affineOpens, (fun W => W), ?_, ?_⟩
  · exact AlgebraicGeometry.iSup_affineOpens_eq_top Y
  · intro W
    exact hasPropertyP_of_isCompact_preimage f (W : Y.Opens) W.property
      ((AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen.mp inferInstance)
        (W : Y.Opens) W.property)

private theorem finiteType_of_topologicallyLocallyNoetherian_target {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] (hY : TopologicallyLocallyNoetherian Y) : FiniteType f := by
  let I := { W : Y.affineOpens // TopologicalSpace.NoetherianSpace (W : Set Y) }
  refine ⟨I, (fun W => W.1), ?_, ?_⟩
  · apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨U, hUopen, hyU, hUnoeth⟩ := hY y
      let Uo : Y.Opens := ⟨U, hUopen⟩
      have hb : ∀ {U : Y.Opens} {x : Y}, x ∈ U →
          ∃ U' ∈ Y.affineOpens, x ∈ U' ∧ U' ≤ U := by
        simpa [TopologicalSpace.Opens.isBasis_iff_nbhd] using
          (AlgebraicGeometry.Scheme.isBasis_affineOpens Y)
      obtain ⟨V, hVaff, hyV, hVU⟩ := hb (U := Uo) (x := y) hyU
      have hVnoeth : TopologicalSpace.NoetherianSpace (V : Set Y) := by
        exact noetherianSpace_of_subset' hUnoeth (by intro z hz; exact hVU hz)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hVaff⟩, hVnoeth⟩, hyV⟩
  · intro W
    exact hasPropertyP_of_isCompact_preimage f (W.1 : Y.Opens) W.1.property
      (isCompact_preimage_of_noetherian_open f (W.1 : Y.Opens) W.2)

theorem immersion_is_of_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]
    (hnoeth : TopologicallyLocallyNoetherian Y ∨ NoetherianSpace X) : FiniteType f := by
  cases hnoeth with
  | inl hY =>
      exact finiteType_of_topologicallyLocallyNoetherian_target f hY
  | inr hX =>
      haveI : TopologicalSpace.NoetherianSpace X := hX
      haveI : QuasiCompact f := AlgebraicGeometry.quasiCompact_of_noetherianSpace_source f
      exact finiteType_of_quasiCompact_locallyOfFiniteType f
