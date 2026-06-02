import Mathlib

open CategoryTheory

/-- Given a local ring A with maximal ideal m, we say that an A-module M is
quasi-finite over A if M/mM has finite rank over the residue field k = A/m. -/
def IsQuasiFiniteModule (A : Type*) [CommRing A] [IsLocalRing A]
  (M : Type*) [AddCommGroup M] [Module A M] : Prop := by sorry

/-- Let f:X→Y be a morphism locally of finite type, and let x be a point of X.
The following conditions are equivalent:
1. The point x is isolated in its fiber f⁻¹(f(x)).
2. The ring O_x is a quasi-finite O_{f(x)}-module. -/
theorem isolated_in_fiber_iff_stalk_quasiFinite {X Y : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [Scheme X] [Scheme Y]
  (f : SchemeHom X Y) (hf : Morphism.LocallyOfFiniteType f) (x : X) :
  (IsIsolatedPtInFiber f x) ↔ 
    IsQuasiFiniteModule (stalk (structureSheaf Y) (f x)) (stalk (structureSheaf X) x) := by sorry
:= by sorry
