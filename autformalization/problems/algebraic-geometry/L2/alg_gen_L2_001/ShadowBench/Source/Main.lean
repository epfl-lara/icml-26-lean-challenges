import Mathlib.AlgebraicGeometry.Noetherian

open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace CategoryTheory

universe u v

/--
Source `docs/source.tex`, line-17 (`isNoetherianRing_of_away`).
The source defines a scheme `X` to be locally Noetherian when `𝒪_X(U)` is Noetherian
for every affine open `U`.  Mathlib already encodes exactly this condition as the
class `AlgebraicGeometry.IsLocallyNoetherian`; this declaration keeps the required
source name as a reducible alias to that class.
-/
def isNoetherianRing_of_away (X : Scheme.{u}) : Prop :=
  AlgebraicGeometry.IsLocallyNoetherian X

/--
Source `docs/source.tex`, line-32 (unnamed claim in the proof of
`isLocallyNoetherian_of_affine_cover`).
Source proof: for each localization map `R → R_{f_i}`, every ideal is the finite
intersection of the comap of its localized extensions; the reverse inclusion is
proved by clearing denominators uniformly and using that the `f_i` generate the
unit ideal.  Applying this equality to an ascending chain of ideals shows the
chain stabilizes because the finitely many localized chains stabilize.
Prover notes: this is the finite-localization Noetherian criterion.  In Mathlib the
corresponding theorem is `AlgebraicGeometry.isNoetherianRing_of_away`, with a
finite set `S : Finset R`, `Ideal.span S = ⊤`, and localizations `Away s`.
-/
theorem isNoetherianRing_of_away_claim
    {R : Type u} [CommRing R] (S : Finset R)
    (hS : Ideal.span (α := R) S = ⊤)
    (hN : ∀ s : S, IsNoetherianRing (Away (M := R) s)) :
    IsNoetherianRing R := by
  exact AlgebraicGeometry.isNoetherianRing_of_away S hS hN

/--
Source `docs/source.tex`, line-21 (`isLocallyNoetherian_of_affine_cover`).
Source proof: use the affine communication lemma.  The property is stable under
basic opens because `Γ(X, U_f) = Γ(X, U)_f` and localizations of Noetherian rings
are Noetherian.  Conversely, for a finite cover by basic opens whose functions
generate the unit ideal, apply the finite-localization claim recorded above.
Prover notes: the Lean statement uses a family `S : ι → X.affineOpens`; the cover
condition is `(⨆ i, S i : X.Opens) = ⊤`, and the section-ring hypothesis is
`∀ i, IsNoetherianRing Γ(X, S i)`.  Mathlib contains the matching theorem
`AlgebraicGeometry.isLocallyNoetherian_of_affine_cover`.
-/
theorem isLocallyNoetherian_of_affine_cover
    {X : Scheme.{u}} {ι : Type v} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤)
    (hS' : ∀ i, IsNoetherianRing Γ(X, S i)) :
    _root_.isNoetherianRing_of_away X := by
  exact AlgebraicGeometry.isLocallyNoetherian_of_affine_cover hS hS'
