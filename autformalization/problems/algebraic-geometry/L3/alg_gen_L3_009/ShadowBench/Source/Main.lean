import Mathlib

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/--
Source definition (`docs/source.tex`, lines 17-28): a morphism of schemes is of finite type
when the target has an affine-open cover whose inverse images are finite unions of affine
opens with finite-type coordinate algebras. This declaration uses Mathlib's equivalent
finite-type package: quasi-compact plus locally of finite type.
-/
class FiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop extends
    AlgebraicGeometry.QuasiCompact f, AlgebraicGeometry.LocallyOfFiniteType f

/--
Source theorem (`docs/source.tex`, lines 30-54): for a finite-type morphism `f : X ⟶ Y`,
`f` is surjective iff for every algebraically closed field `Ω`, postcomposition with `f`
surjects from `Ω`-points of `X` to `Ω`-points of `Y`.

Source proof: the reverse implication tests a point `y : Y` by extending its residue field
`κ(y)` to an algebraically closed field `Ω`; a lift of the resulting `Ω`-point gives a
preimage in `X`. For the forward implication, pull back along an arbitrary
`g : Spec Ω ⟶ Y`; surjectivity makes the finite-type fiber product nonempty, and a
nonempty affine open in it has a nonzero finite-type `Ω`-algebra of functions. The
Nullstellensatz gives an `Ω`-algebra map to `Ω`, hence an `Ω`-rational point/section and
therefore a lift.

Prover notes: represent `X(Ω)` as `Spec (.of Ω) ⟶ X`; the induced map is `p ↦ p ≫ f`.
Likely useful facts include `Scheme.SpecToEquivOfField`, residue-field maps,
base-change stability of `QuasiCompact` and `LocallyOfFiniteType`, and the algebraically
closed-field form of Nullstellensatz.
-/
theorem surjective_iff_surjective_on_algClosed_points_of_finiteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] :
    Function.Surjective f ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Surjective
          (fun (p : AlgebraicGeometry.Spec (.of Ω) ⟶ X) => p ≫ f) := by
  classical
  constructor
  · intro hf Ω _ _ g
    letI : AlgebraicGeometry.Surjective f := ⟨hf⟩
    let P : Scheme.{u} := Limits.pullback f g
    haveI : JacobsonSpace P := by
      dsimp [P]
      exact LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd f g)
    have hPnonempty : Nonempty P := by
      have hsurj_snd : Function.Surjective (Limits.pullback.snd f g) :=
        (Limits.pullback.snd f g).surjective
      obtain ⟨z, hz⟩ := hsurj_snd (IsLocalRing.closedPoint Ω)
      exact ⟨z⟩
    obtain ⟨z, hz⟩ : ((Set.univ : Set P) ∩ closedPoints P).Nonempty := by
      exact nonempty_inter_closedPoints (Z := (Set.univ : Set P)) Set.univ_nonempty
        isClosed_univ.isLocallyClosed
    let s : AlgebraicGeometry.Spec (.of Ω) ⟶ P :=
      pointOfClosedPoint (Limits.pullback.snd f g) z hz.2
    refine ⟨s ≫ Limits.pullback.fst f g, ?_⟩
    calc
      (s ≫ Limits.pullback.fst f g) ≫ f = s ≫ (Limits.pullback.fst f g ≫ f) := by
        simp [Category.assoc]
      _ = s ≫ (Limits.pullback.snd f g ≫ g) := by
        rw [Limits.pullback.condition]
      _ = (s ≫ Limits.pullback.snd f g) ≫ g := by
        simp [Category.assoc]
      _ = 𝟙 _ ≫ g := by
        rw [pointOfClosedPoint_comp]
      _ = g := by simp
  · intro h y
    let Ω : Type u := AlgebraicClosure (Y.residueField y)
    let φ : Y.residueField y ⟶ CommRingCat.of Ω :=
      CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)
    let g : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ Y :=
      AlgebraicGeometry.Spec.map φ ≫ Y.fromSpecResidueField y
    obtain ⟨p, hp⟩ := h Ω g
    refine ⟨p (IsLocalRing.closedPoint Ω), ?_⟩
    change (p ≫ f) (IsLocalRing.closedPoint Ω) = y
    have hp' := congrArg
      (fun q : AlgebraicGeometry.Spec (.of Ω) ⟶ Y => q (IsLocalRing.closedPoint Ω)) hp
    simpa [g] using hp'
