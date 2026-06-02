import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Etale.QuasiFinite

open CategoryTheory Limits

theorem Scheme.Hom.exists_isIso_morphismRestrict_toNormalization 
  (X Y Y' : Scheme) 
  (f : X → Y) 
  (f' : X → Y') 
  (ν : Y' → Y) 
  (h_factor : f = ν ∘ f')
  (h_finite_type : FiniteType f)
  (h_separated : IsSeparated f)
  (h_normalization : IsNormalization ν) :
  ∃ U' : OpenSubscheme Y', 
    (IsIsomorphism (f'.restrict (U' : Set Y'))) ∧
    ((f' ⁻¹ U').carrier = {x : X | IsQuasiFiniteAt f x}) := by sorry
:= by sorry
