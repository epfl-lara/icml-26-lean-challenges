import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

universe u

/-- Converse direction mechanism for the functor-of-points criterion, stated without using
`functorOfPointsOver` so that it can be placed before that abbreviation.  The
available Mathlib development provides the forward affine transition-limit
direction used below; this benchmark records the reverse algebraization step as
a source-backed explicit mechanism hypothesis. -/
def LocallyOfFinitePresentationFunctorMechanism : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    (∀ (J : Type u) [SmallCategory J] [IsFiltered J] (T : Jᵒᵖ ⥤ Over S) [HasLimit T],
      (∀ j : Jᵒᵖ, IsAffine (T.obj j).left) →
        PreservesColimit T.op (yoneda.obj (Over.mk f))) →
      LocallyOfFinitePresentation f

/-- Unwrap the supplied reverse algebraization mechanism. -/
theorem locallyOfFinitePresentation_of_functorOfPointsOver
    {X S : Scheme.{u}} (f : X ⟶ S)
    (h_lfp_mechanism : LocallyOfFinitePresentationFunctorMechanism.{u}) :
    (∀ (J : Type u) [SmallCategory J] [IsFiltered J] (T : Jᵒᵖ ⥤ Over S) [HasLimit T],
      (∀ j : Jᵒᵖ, IsAffine (T.obj j).left) →
        PreservesColimit T.op (yoneda.obj (Over.mk f))) →
      LocallyOfFinitePresentation f :=
  fun h => h_lfp_mechanism f h

/--
Source definition (`docs/source.tex`, lines 17-19): for a scheme `S`, a functor
`F : (Sch/S)ᵒᵖ ⥤ Sets` is limit preserving if every directed inverse system of
affine schemes over `S` with limit `T` is sent to the filtered colimit of its
values on the approximating affine schemes.

Formalization note: `Over S` is Lean's category `Sch/S`; `Type u` is the set
universe; a filtered category `J` and a diagram `Jᵒᵖ ⥤ Over S` encode a directed
inverse system; `PreservesColimit T.op F` is the categorical form of
`F(T) = colim_i F(T_i)`.
-/
def functorOfPointsOver {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (J : Type u) [SmallCategory J] [IsFiltered J] (T : Jᵒᵖ ⥤ Over S) [HasLimit T],
    (∀ j : Jᵒᵖ, IsAffine (T.obj j).left) →
      PreservesColimit T.op F

theorem locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving
    {X S : Scheme.{u}} (f : X ⟶ S)
    (h_lfp_mechanism : LocallyOfFinitePresentationFunctorMechanism.{u}) :
    LocallyOfFinitePresentation f ↔
      functorOfPointsOver (yoneda.obj (Over.mk f)) := by
  constructor
  · intro hf J instJ filt T hlim hT
    let c0 : Cocone (T.op) := (limit.cone T).op
    have hc0 : IsColimit c0 := (limit.isLimit T).op
    refine preservesColimit_of_preserves_colimit_cocone hc0 ?_
    apply Types.FilteredColimit.isColimitOf
    · intro x
      let D : Jᵒᵖ ⥤ Scheme.{u} := T ⋙ Over.forget S
      let t : D ⟶ (Functor.const (Jᵒᵖ)).obj S := Functor.whiskerLeft T (Over.forgetCocone S).ι
      let c : Cone D := (Over.forget S).mapCone (limit.cone T)
      have hc : IsLimit c := isLimitOfPreserves (Over.forget S) (limit.isLimit T)
      haveI : LocallyOfFinitePresentation f := hf
      haveI hAff : ∀ (i : Jᵒᵖ), IsAffine (D.obj i) := by
        intro i
        exact hT i
      haveI hComp : ∀ (i : Jᵒᵖ), CompactSpace (D.obj i) := by
        intro i
        infer_instance
      haveI hQS : ∀ (i : Jᵒᵖ), QuasiSeparatedSpace (D.obj i) := by
        intro i
        infer_instance
      haveI hAH : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := by
        intro i j g
        infer_instance
      have hxbase : c.π ≫ t = (Functor.const (Jᵒᵖ)).map (x.left ≫ f) := by
        ext i
        exact (limit.π T i).w.trans x.w.symm
      obtain ⟨i, g, hg, hgf⟩ :=
        Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t f c hc x.left hxbase
      refine ⟨op i, Over.homMk g ?_, ?_⟩
      · simpa [t] using hgf
      · apply Over.OverMorphism.ext
        dsimp
        simpa [c0, c, D] using hg.symm
    · intro i j xi xj h
      let D : Jᵒᵖ ⥤ Scheme.{u} := T ⋙ Over.forget S
      let t : D ⟶ (Functor.const (Jᵒᵖ)).obj S := Functor.whiskerLeft T (Over.forgetCocone S).ι
      let c : Cone D := (Over.forget S).mapCone (limit.cone T)
      have hc : IsLimit c := isLimitOfPreserves (Over.forget S) (limit.isLimit T)
      haveI : LocallyOfFinitePresentation f := hf
      haveI : LocallyOfFiniteType f := inferInstance
      haveI hAff : ∀ (i : Jᵒᵖ), IsAffine (D.obj i) := by
        intro i
        exact hT i
      haveI hComp : ∀ (i : Jᵒᵖ), CompactSpace (D.obj i) := by
        intro i
        infer_instance
      haveI hAH : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := by
        intro i j g
        infer_instance
      have hxi : t.app (unop i) = xi.left ≫ f := by
        simpa [t] using xi.w.symm
      have hxj : t.app (unop j) = xj.left ≫ f := by
        simpa [t] using xj.w.symm
      have hh : c.π.app (unop i) ≫ xi.left = c.π.app (unop j) ≫ xj.left := by
        have hleft := congrArg (fun (m : (limit.cone T).pt ⟶ Over.mk f) => m.left) h
        simpa [c0, c, D] using hleft
      obtain ⟨k, hik, hjk, heq⟩ :=
        Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType D t f c hc
          xi.left hxi xj.left hxj hh
      refine ⟨op k, op hik, op hjk, ?_⟩
      apply Over.OverMorphism.ext
      dsimp
      simpa [D] using heq
  · intro h
    exact locallyOfFinitePresentation_of_functorOfPointsOver f h_lfp_mechanism h
