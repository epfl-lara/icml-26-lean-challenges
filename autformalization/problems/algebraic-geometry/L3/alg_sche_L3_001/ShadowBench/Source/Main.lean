import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

universe u

open CategoryTheory Opposite
open AlgebraicGeometry

/--
ShadowBench problem `algebraic-geometry/L3/alg_sche_L3_001`, source theorem `toΓSpec`.

Source proof: for a point `x`, restrict global sections to an affine neighbourhood and then to
`𝒪_{X,x}`; the prime ideal is the preimage of the non-units (the closed point) of the local
stalk under the germ map. The induced map from the localization at the complement is local
because a fraction `r / s` is nonunit at the stalk exactly when `r` lies in that prime.

Prover notes: Mathlib's canonical morphism is `Scheme.toSpecΓ`. The pointwise formula is
`Scheme.toSpecΓ_apply`, where `IsLocalRing.closedPoint` records the ideal of nonunits in the
stalk, so the formula expresses the source's prime ideal of sections not mapping to stalk units.
The source-facing alias `toΓSpec` below preserves the theorem name from the document.
-/
theorem toGammaSpec (X : Scheme.{u}) :
    ∃ φ : X ⟶ Spec Γ(X, ⊤),
      φ = X.toSpecΓ ∧
        ∀ x : X, φ x = Spec.map (X.presheaf.Γgerm x) (IsLocalRing.closedPoint _) := by
  refine ⟨X.toSpecΓ, rfl, ?_⟩
  intro x
  exact Scheme.toSpecΓ_apply X x

alias toΓSpec := toGammaSpec
