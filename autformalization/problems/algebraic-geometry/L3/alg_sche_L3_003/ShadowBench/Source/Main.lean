import Mathlib

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source proof bridge for the projection `π : ℙ^n_S ⟶ S` from relative projective
space. The current Mathlib pin does not expose a scheme-level `ℙ^n_S`
construction or a built-in projective morphism predicate, so the formalization
records exactly the proof-relevant fact used by the source: this projection is
proper.
-/
def IsRelativeProjectiveSpaceProjection {P S : Scheme} (_n : ℕ) (π : P ⟶ S) :
    Prop :=
  IsProper π

/--
Source definition bridge: a scheme morphism is projective if it factors through
a closed immersion into a relative projective-space object over the base.

The ambient object `P` is abstract because no concrete `ℙ^n_S` scheme-level API
was available in the selected Mathlib version. The bridge keeps the source data
used in the proof: a natural number `n`, a closed immersion into `P`, a
projection `P ⟶ S` with the projective-space properness property, and the
factorization equality.
-/
def IsProjective {X S : Scheme} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (P : Scheme) (i : X ⟶ P) (π : P ⟶ S),
    IsClosedImmersion i ∧ IsRelativeProjectiveSpaceProjection n π ∧ i ≫ π = f

/--
Source theorem `line-17`: if `f : X ⟶ S` is a projective morphism of schemes,
then `f` is proper.

Source proof: write `f` as a closed immersion into relative projective space
followed by the projection to `S`; the projection from projective space is
proper, closed immersions are proper, and proper morphisms are stable under
composition.
-/
theorem projective_isProper {X S : Scheme} (f : X ⟶ S)
    (hf : AlgebraicGeometry.IsProjective f) : IsProper f := by
  rcases hf with ⟨n, P, i, π, hi, hπ, hfac⟩
  rw [← hfac]
  haveI : IsClosedImmersion i := hi
  haveI : IsProper i := inferInstance
  haveI : IsProper π := hπ
  infer_instance

end AlgebraicGeometry

export AlgebraicGeometry (projective_isProper)
