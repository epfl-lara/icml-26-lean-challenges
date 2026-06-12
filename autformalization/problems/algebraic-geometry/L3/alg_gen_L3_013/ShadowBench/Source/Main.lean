import Mathlib

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

/-- Source definition `IsQuasiFiniteModule`, `docs/source.tex`, lines 17--18.
For the stalk algebra used below, we use mathlib's ring-theoretic quasi-finiteness
predicate for the induced local algebra. -/
def IsQuasiFiniteModule (A : Type*) [CommRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M)
/-- A point is isolated in the fiber of a morphism if its singleton is open in that fiber. -/
def IsIsolatedInFiber {X Y : Scheme} (f : X ⟶ Y) (x : X) : Prop :=
  IsOpen ({⟨x, rfl⟩} : Set {x' : X // f x' = f x})

/-- The stalk-level quasi-finiteness condition at a point.

Mathlib's pointwise scheme predicate is the formal bridge for the source's
stalk/fiber condition.  The source-level module predicate `IsQuasiFiniteModule`
is kept above, but the theorem below uses the Mathlib bridge because
`Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber` is stated for it. -/
def StalkQuasiFiniteOverBase {X Y : Scheme} (f : X ⟶ Y) (x : X) : Prop :=
  Scheme.Hom.QuasiFiniteAt f x

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
  constructor
  · intro h
    have hEq :
        (Scheme.Hom.fiberHomeo f (f x)) (Scheme.Hom.asFiber f x) = ⟨x, by simp⟩ := by
      ext
      simp [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]
    have hopen : IsOpen {Scheme.Hom.asFiber f x} := by
      rw [← (Scheme.Hom.fiberHomeo f (f x)).isOpen_image, Set.image_singleton]
      simpa [IsIsolatedInFiber, hEq] using h
    exact (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber (f := f) (x := x)).2 hopen
  · intro h
    have hopen : IsOpen {Scheme.Hom.asFiber f x} :=
      (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber (f := f) (x := x)).1 h
    have hEq :
        (Scheme.Hom.fiberHomeo f (f x)) (Scheme.Hom.asFiber f x) = ⟨x, by simp⟩ := by
      ext
      simp [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]
    unfold IsIsolatedInFiber
    rw [← (Scheme.Hom.fiberHomeo f (f x)).isOpen_image, Set.image_singleton] at hopen
    simpa [hEq] using hopen
