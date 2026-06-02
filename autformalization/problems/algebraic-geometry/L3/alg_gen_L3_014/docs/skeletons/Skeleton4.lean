import Mathlib

theorem quasiSeparated_iff_preimage_isQuasiSeparated_of_openCover 
  {X Y : Type*} [Scheme X] [Scheme Y] 
  (f : X → Y) 
  (U : Type*) [DecidableEq U] 
  (hU : ∀ u : U, IsOpen (U u)) 
  (hcover : ∀ y : Y, ∃ u : U, y ∈ U u)
  (hquasi : ∀ u : U, IsQuasiSeparated (U u)) :
  IsQuasiSeparated f ↔ ∀ u : U, IsQuasiSeparated (f ⁻¹' (U u)) := by sorry
:= by sorry
