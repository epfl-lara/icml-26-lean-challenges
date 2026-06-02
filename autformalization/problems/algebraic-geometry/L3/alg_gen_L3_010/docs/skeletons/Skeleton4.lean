import Mathlib

open CategoryTheory Opposite
open TopologicalSpace

theorem isAffineOpen_inf_preimage {X Y : Type*} [Scheme X] [Scheme Y] 
    [Separated Y] (f : SchemeMorphism X Y) 
    (U : OpenSubscheme X) (V : OpenSubscheme Y)
    (hU_aff : U.IsAffine) (hV_aff : V.IsAffine) :
    IsAffine (U ∩ f.pullback V) := by sorry
:= by sorry
