import Mathlib
import ShadowBench.Source.ProjectiveStability

open CategoryTheory

namespace AlgebraicGeometry

open CategoryTheory Limits

noncomputable section

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

/-- Relative projective space over `S`, represented as base change of the absolute model. -/
def projectiveSpace (n : ℕ) (S : Scheme) : Scheme :=
  pullback (terminal.from S) (terminal.from (standardProjectiveSpace n))

/-- The structural morphism `ℙ^n_S ⟶ S`. -/
def projectiveSpaceToBase (n : ℕ) (S : Scheme) : projectiveSpace n S ⟶ S :=
  pullback.fst _ _

/-- A scheme morphism is projective if its source admits a closed immersion into some relative
projective space over the target. -/
def IsProjective {X S : Scheme} (f : X ⟶ S) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ projectiveSpace n S,
    IsClosedImmersion i ∧ i ≫ projectiveSpaceToBase n S = f

end

end AlgebraicGeometry

open CategoryTheory AlgebraicGeometry

theorem prod_projective {S X Y : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    (hX : AlgebraicGeometry.IsProjective f) (hY : AlgebraicGeometry.IsProjective g) :
    AlgebraicGeometry.IsProjective (CategoryTheory.Limits.pullback.fst f g ≫ f) := by
  exact isProjective_comp
    (isProjective_pullback_fst (f := f) (g := g) hY) hX
