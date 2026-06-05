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
  sorry

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
theorem immersion_is_of_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]
    (hnoeth : TopologicallyLocallyNoetherian Y ∨ NoetherianSpace X) : FiniteType f := by
  sorry
