import Mathlib

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

/-- Source definition `IsQuasiFiniteModule`, `docs/source.tex`, lines 17--18.
For a local ring `A`, this records that the special fiber `κ(A) ⊗[A] M`, i.e. the
quotient of `M` by the action of the maximal ideal of `A`, is finite-dimensional over the
residue field `κ(A)`. -/
def IsQuasiFiniteModule (A : Type*) [CommRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M)

/-- The point `x` is isolated in the set-theoretic fiber of a scheme morphism `f` if
its singleton is open in the subspace topology on `{x' // f x' = f x}`. -/
def IsIsolatedInFiber {X Y : Scheme} (f : X ⟶ Y) (x : X) : Prop :=
  IsOpen ({⟨x, rfl⟩} : Set {x' : X // f x' = f x})

/-- The stalk `𝒪_{X,x}` as an `𝒪_{Y,f(x)}`-module via the stalk map induced by `f` is
quasi-finite. -/
def StalkQuasiFiniteOverBase {X Y : Scheme} (f : X ⟶ Y) (x : X) : Prop :=
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  IsQuasiFiniteModule (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- Source theorem `isolated_in_fiber_iff_stalk_quasiFinite`, `docs/source.tex`, lines 19--33.

Source proof: the assertion is local on source and target. Reduce to an affine finite-type
map `Spec A → Spec B`, then replace the target by `Spec 𝒪_{f(x)}` so that `B` is local.
The fiber is `Spec (A / 𝔫 A)` over the residue field `B / 𝔫`. If `x` is isolated in the
fiber, localizing around `x` reduces the fiber to one point, hence the fiber algebra is a
finite-dimensional vector space over the residue field, which is exactly quasi-finiteness of
the stalk module. Conversely, if the stalk is quasi-finite, the corresponding affine fiber is
Artinian and therefore discrete, so `x` is isolated in the fiber.

Prover notes: use `AlgebraicGeometry.LocallyOfFiniteType` for the hypothesis and the stalk
module structure coming from `f.stalkMap x`; `IsIsolatedInFiber` is encoded as openness of the
singleton in the subspace fiber. The full EGA-style result may require affine-local reduction,
base change to the local target, finite-dimensionality of the special fiber, and Artinian
scheme discreteness lemmas. -/
theorem isolated_in_fiber_iff_stalk_quasiFinite {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    IsIsolatedInFiber f x ↔ StalkQuasiFiniteOverBase f x := by
  sorry
