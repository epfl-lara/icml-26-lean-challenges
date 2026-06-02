import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace CategoryTheory

-- Definition: A scheme X is locally Noetherian if O_X(U) is Noetherian for every affine open U
def isNoetherianRing_of_away (X : Scheme) : Prop := 
  ∀ U : OpenSubscheme X, IsAffineOpen U → IsNoetherianRing (structureSheaf X U)

-- Theorem: If a scheme X has an affine open covering where each section ring is Noetherian, then X is locally Noetherian
theorem isLocallyNoetherian_of_affine_cover (X : Scheme) 
  (I : Type*) [Nonempty I] 
  (U : I → OpenSubscheme X)
  (h_cover : ∀ x : X, ∃ i : I, x ∈ U i)
  (h_affine : ∀ i : I, IsAffineOpen (U i))
  (h_noetherian : ∀ i : I, IsNoetherianRing (structureSheaf X (U i))) :
  isNoetherianRing_of_away X := by sorry
