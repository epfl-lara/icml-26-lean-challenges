import Mathlib

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

noncomputable section

/--
Integral model of projective `n`-space, realized as `Proj` of the standard homogeneous grading on
`ULift ℤ[x₀, ..., xₙ]`. The coordinate index type is `Fin (n + 1)`, matching the source convention
that `\mathbf{P}^n` has `n + 1` homogeneous coordinates.
-/
abbrev ProjectiveSpaceModel (n : ℕ) : Scheme.{u} := by
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  exact Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))

/--
Projective space `\mathbf{P}^n_S` over a base scheme `S`, defined by base change of the integral
model of projective space along the unique map from `S` to the terminal scheme.
-/
def ProjectiveSpace (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (ProjectiveSpaceModel.{u} n))

namespace ProjectiveSpace

instance instCanonicallyOver (n : ℕ) (S : Scheme.{u}) :
    (ProjectiveSpace n S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The structure morphism `\pi : \mathbf{P}^n_S \to S`. -/
def π (n : ℕ) (S : Scheme.{u}) : ProjectiveSpace n S ⟶ S :=
  ProjectiveSpace n S ↘ S

end ProjectiveSpace

/--
Source definition (docs/source.tex, lines 17--27): a morphism `f : X \to S` of schemes is
Hartshorne-projective if it factors through a closed immersion into `\mathbf{P}^n_S` for some
`n ≥ 0`, followed by the structure morphism to `S`.
-/
def IsProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace n S),
    IsClosedImmersion i ∧ i ≫ ProjectiveSpace.π n S = f

/--
Source proof (docs/source.tex, lines 37--47): projective space over `S` is finite type, separated,
and universally closed. Universal closedness is shown by the valuative criterion: scale homogeneous
coordinates over a valuation ring so they lie in the ring and one is a unit, giving the required
extension; uniqueness follows from separatedness.

Prover notes: search for existing properness theorems for `Proj`/projective space first. Otherwise
unfold `IsProper` via finite type, separatedness, and universal closedness; the finite affine cover
by the standard opens `D_+(x_i)` and the valuative criterion are the source proof strategy.
-/
theorem is_projective_proper (S : Scheme.{u}) (n : ℕ) :
    IsProper (ProjectiveSpace.π n S) := by
  let A := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)
  letI : GradedAlgebra A := MvPolynomial.gradedAlgebra
  have hA0fg : (A 0).FG := by
    change (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0).FG
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_span]
    exact Submodule.fg_span_singleton (R := ULift.{u} ℤ)
      (x := (1 : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)))
  have hA0finite : Module.Finite (ULift.{u} ℤ) (A 0) := Module.Finite.iff_fg.mpr hA0fg
  have hC (r : ULift.{u} ℤ) : MvPolynomial.C r ∈ A 0 := by
    change MvPolynomial.C r ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_span]
    exact (Submodule.mem_span_singleton).mpr ⟨r, by
      calc
        r • (1 : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) =
            (algebraMap (ULift.{u} ℤ) (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) r) * 1 :=
          Algebra.smul_def r (1 : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))
        _ = MvPolynomial.C r := by simp⟩
  have hfiniteType : Algebra.FiniteType (A 0) (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) := by
    let f : MvPolynomial (Fin (n + 1)) (A 0) →ₐ[A 0]
        MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) :=
      MvPolynomial.aeval (fun i : Fin (n + 1) => MvPolynomial.X i)
    have hf : Function.Surjective f := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r =>
          refine ⟨MvPolynomial.C (⟨MvPolynomial.C r, hC r⟩ : A 0), ?_⟩
          dsimp [f]
          rw [MvPolynomial.aeval_C]
          rfl
      | add p q hp hq =>
          rcases hp with ⟨p', hp'⟩
          rcases hq with ⟨q', hq'⟩
          refine ⟨p' + q', ?_⟩
          calc
            f (p' + q') = f p' + f q' := map_add f p' q'
            _ = p + q := by rw [hp', hq']
      | mul_X p i hp =>
          rcases hp with ⟨p', hp'⟩
          refine ⟨p' * MvPolynomial.X i, ?_⟩
          calc
            f (p' * MvPolynomial.X i) = f p' * f (MvPolynomial.X i) :=
              map_mul f p' (MvPolynomial.X i)
            _ = p * MvPolynomial.X i := by
              rw [hp']
              dsimp [f]
              rw [MvPolynomial.aeval_X]
    exact Algebra.FiniteType.of_surjective f hf
  have hSpecA0 : IsProper (terminal.from (Spec (CommRingCat.of (A 0)))) := by
    haveI : Module.Finite (ULift.{u} ℤ) (A 0) := hA0finite
    let g : Spec (CommRingCat.of (A 0)) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (A 0)))
    have hgfin : IsFinite g := by
      dsimp [g]
      rw [IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ULift.{u} ℤ) (B := A 0)).mpr hA0finite
    have hg : IsProper g := by
      dsimp [g] at hgfin ⊢
      infer_instance
    let e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
      (terminalIsTerminal : IsTerminal (⊤_ Scheme.{u})).uniqueUpToIso specULiftZIsTerminal
    have hcomp : IsProper (terminal.from (Spec (CommRingCat.of (A 0))) ≫ e.hom) := by
      have heq : terminal.from (Spec (CommRingCat.of (A 0))) ≫ e.hom = g := by
        apply specULiftZIsTerminal.hom_ext
      rw [heq]
      exact hg
    exact (MorphismProperty.cancel_right_of_respectsIso (@IsProper)
      (terminal.from (Spec (CommRingCat.of (A 0)))) e.hom).mp hcomp
  have hProj : IsProper (Proj.toSpecZero A) := by
    haveI : Algebra.FiniteType (A 0) (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) := hfiniteType
    infer_instance
  have hModel : IsProper (terminal.from (ProjectiveSpaceModel.{u} n)) := by
    haveI : IsProper (Proj.toSpecZero A) := hProj
    haveI : IsProper (terminal.from (Spec (CommRingCat.of (A 0)))) := hSpecA0
    change IsProper (terminal.from (Proj A))
    rw [← terminal.comp_from (Proj.toSpecZero A)]
    infer_instance
  haveI : IsProper (terminal.from (ProjectiveSpaceModel.{u} n)) := hModel
  change IsProper (pullback.fst (terminal.from S) (terminal.from (ProjectiveSpaceModel.{u} n)))
  infer_instance

/--
Source proof (docs/source.tex, lines 53--60): if `f` is projective, choose a factorization
`X --i--> \mathbf{P}^n_S --π--> S` with `i` a closed immersion. Closed immersions are proper,
`π` is proper by `is_projective_proper`, and proper morphisms are stable under composition; rewrite
along the factorization equality to obtain properness of `f`.

Prover notes: unfold `IsProjective` to get witnesses `n`, `i`, `IsClosedImmersion i`, and
`i ≫ ProjectiveSpace.π n S = f`; combine properness of closed immersions with
`is_projective_proper S n` using properness stability under composition, then rewrite.
-/
theorem projective_isProper {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsProjective f) :
    IsProper f := by
  rcases hf with ⟨n, i, hi, hfac⟩
  rw [← hfac]
  haveI : IsClosedImmersion i := hi
  haveI : IsProper (ProjectiveSpace.π n S) := is_projective_proper S n
  infer_instance

end

end AlgebraicGeometry

export AlgebraicGeometry (IsProjective is_projective_proper projective_isProper)
