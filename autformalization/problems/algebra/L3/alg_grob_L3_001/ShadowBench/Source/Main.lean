import Mathlib

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

/--
Source definition `line-17`: a finite morphism of schemes is affine and has finite
coordinate algebra on affine opens. This project-level name is a wrapper around Mathlib's
`AlgebraicGeometry.IsFinite`, whose affine-local definition matches the source statement.
-/
def IsFinite {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.IsFinite f

/-- The standard absolute projective space used for the source theorem: `Proj` of the standard
`ℤ`-graded polynomial ring with `n + 1` homogeneous coordinates. -/
def standardProjectiveSpace (n : ℕ) : Scheme := by
  let 𝒜 : ℕ → Submodule (ULift ℤ) (MvPolynomial (Fin (n + 1)) (ULift ℤ)) :=
    MvPolynomial.weightedHomogeneousSubmodule (ULift ℤ)
      (fun _ : Fin (n + 1) => (1 : ℕ))
  letI : GradedRing 𝒜 :=
    MvPolynomial.weightedGradedAlgebra (ULift ℤ)
      (fun _ : Fin (n + 1) => (1 : ℕ))
  exact Proj 𝒜

/-- Relative projective space `ℙ^n_Y` over `Y`, represented as base change of the absolute model
along the terminal morphisms (`Spec ℤ` is terminal in `Scheme`). -/
def projectiveSpace (n : ℕ) (Y : Scheme) : Scheme :=
  pullback (terminal.from Y) (terminal.from (standardProjectiveSpace n))

/-- The structural projection `ℙ^n_Y ⟶ Y`. -/
def projectiveSpaceToBase (n : ℕ) (Y : Scheme) : projectiveSpace n Y ⟶ Y :=
  pullback.fst _ _

/--
Source definition `line-23`: a morphism is projective when its source admits a closed immersion
into some relative projective space `ℙ^n_Y` over the target, compatible with the projection.

This is the genuine definition of a projective morphism: `ℙ^n_Y` is constructed as `Proj` of the
standard graded polynomial ring base-changed to `Y`, and properness of the projection is *not*
assumed (so the theorem below is not trivialized). Earlier the bridge carried an arbitrary
`space` with no projective-space constraint, which made `IsProjective` hold for every morphism;
this construction removes that vacuity.
-/
def IsProjective {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ projectiveSpace n Y,
    IsClosedImmersion i ∧ i ≫ projectiveSpaceToBase n Y = f

/--
Source theorem `line-35`: finite morphisms of schemes are projective.

Source proof: the statement is local on `Y`; after reducing to `Y = Spec A` and
`X = Spec B` with `B` finite over `A`, choose finite module generators of `B`, present
`B` as a quotient of a polynomial algebra `A[x₁, …, xₙ]`, obtaining a closed immersion
`X ↪ 𝔸^n_Y`. Composing with the standard open immersion `𝔸^n_Y ↪ ℙ^n_Y` and using that finite
morphisms are proper, `X` is realized as a closed subscheme of `ℙ^n_Y`, so `f` factors as a
closed immersion into `ℙ^n_Y` followed by the projection to `Y`.

Prover notes: unfold `IsFinite` to Mathlib's `AlgebraicGeometry.IsFinite`; finite ⟹ proper is
available as an instance (`AlgebraicGeometry.IsProper` of a finite morphism). The projective-space
bridge `projectiveSpace`/`projectiveSpaceToBase` constructs `ℙ^n_Y` genuinely via `Proj`.
-/
theorem finite_implies_projective {X Y : Scheme} (f : X ⟶ Y)
    (hf : _root_.IsFinite f) : _root_.IsProjective f := by
  sorry

end
