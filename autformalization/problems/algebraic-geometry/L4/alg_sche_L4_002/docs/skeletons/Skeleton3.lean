import Mathlib

open CategoryTheory AlgebraicGeometry

theorem prod_projective (S : Scheme) (X Y : Scheme) 
  (hX : IsProjective S X) (hY : IsProjective S Y) :
  IsProjective S (X ×_S Y) := by sorry
