import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

-- Assuming appropriate type classes and definitions for schemes and morphisms 
-- are available in the context

/-- A flat morphism of finite type of Noetherian schemes is an open morphism -/
theorem flat_is_open (X Y : Type*) [NoetherianScheme X] [NoetherianScheme Y] 
  (f : X → Y) (hf_flat : IsFlat f) (hf_finite : IsOfFiniteType f) : 
  IsOpenMap f := by sorry

/-- For a flat morphism of finite type of Noetherian schemes, the image of an open subset is open -/
theorem flat_open_image (X Y : Type*) [NoetherianScheme X] [NoetherianScheme Y] 
  (f : X → Y) (hf_flat : IsFlat f) (hf_finite : IsOfFiniteType f) 
  (U : Set X) (hU : IsOpen U) : 
  IsOpen (f '' U) := by sorry

/-- For a flat morphism, the complement of the image intersected with an affine open subset 
    equals the vanishing set of some ideal -/
theorem flat_morphism_complement_of_image_is_closed (X Y : Type*) [Scheme X] [Scheme Y] 
  (f : X → Y) (hf_flat : IsFlat f) 
  (U : Set X) (hU : IsOpen U) 
  (B : Type*) [CommRing B] (V : Set Y) (hV : IsOpen V) 
  (hV_affine : ∃ (ψ : Y → Spec B), IsOpenMap ψ ∧ ψ '' V = Set.univ) :
  ∃ I : Ideal B, V \ (f '' U ∩ V) = {y ∈ V | ∃ p : Ideal B, I ≤ p ∧ y = ψ ⟨p, sorry⟩} := by sorry
:= by sorry
