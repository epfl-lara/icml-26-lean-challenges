import Mathlib

open CategoryTheory AlgebraicGeometry

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

/-- Relative projective space `ℙ^n_S` over `S`, represented as base change of the absolute model
along the terminal morphisms (`Spec ℤ` is terminal in `Scheme`). -/
def projectiveSpace (n : ℕ) (S : Scheme) : Scheme :=
  pullback (terminal.from S) (terminal.from (standardProjectiveSpace n))

/-- The structural projection `ℙ^n_S ⟶ S`. -/
def projectiveSpaceToBase (n : ℕ) (S : Scheme) : projectiveSpace n S ⟶ S :=
  pullback.fst _ _

/-- A scheme morphism is projective if its source admits a closed immersion into some relative
projective space over the target, compatible with the projection. This is the genuine definition
of a projective morphism; the properness of the projection `ℙ^n_S ⟶ S` is *not* assumed. -/
def IsProjective {X S : Scheme} (f : X ⟶ S) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ projectiveSpace n S,
    IsClosedImmersion i ∧ i ≫ projectiveSpaceToBase n S = f

end

end AlgebraicGeometry

open CategoryTheory AlgebraicGeometry

set_option synthInstance.maxHeartbeats 200000 in
/-- The projection from the relative standard projective space to its base is proper. -/
theorem projectiveSpaceToBase_isProper (n : ℕ) (S : Scheme) :
    IsProper (projectiveSpaceToBase n S) := by
  let A := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift ℤ)
  letI : GradedAlgebra A := MvPolynomial.gradedAlgebra
  have hA0fg : (A 0).FG := by
    change (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift ℤ) 0).FG
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_span]
    exact Submodule.fg_span_singleton (R := ULift ℤ)
      (x := (1 : MvPolynomial (Fin (n + 1)) (ULift ℤ)))
  have hA0finite : Module.Finite (ULift ℤ) (A 0) := Module.Finite.iff_fg.mpr hA0fg
  have hC (r : ULift ℤ) : MvPolynomial.C r ∈ A 0 := by
    change MvPolynomial.C r ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift ℤ) 0
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_span]
    exact (Submodule.mem_span_singleton).mpr ⟨r, by
      calc
        r • (1 : MvPolynomial (Fin (n + 1)) (ULift ℤ)) =
            (algebraMap (ULift ℤ) (MvPolynomial (Fin (n + 1)) (ULift ℤ)) r) * 1 :=
          Algebra.smul_def r (1 : MvPolynomial (Fin (n + 1)) (ULift ℤ))
        _ = MvPolynomial.C r := by simp⟩
  have hfiniteType : Algebra.FiniteType (A 0) (MvPolynomial (Fin (n + 1)) (ULift ℤ)) := by
    let f : MvPolynomial (Fin (n + 1)) (A 0) →ₐ[A 0]
        MvPolynomial (Fin (n + 1)) (ULift ℤ) :=
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
  have hSpecA0 : IsProper (CategoryTheory.Limits.terminal.from (Spec (CommRingCat.of (A 0)))) := by
    haveI : Module.Finite (ULift ℤ) (A 0) := hA0finite
    let g : Spec (CommRingCat.of (A 0)) ⟶ Spec (CommRingCat.of (ULift ℤ)) :=
      Spec.map (CommRingCat.ofHom (algebraMap (ULift ℤ) (A 0)))
    have hgfin : IsFinite g := by
      dsimp [g]
      rw [IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ULift ℤ) (B := A 0)).mpr hA0finite
    have hg : IsProper g := by
      dsimp [g] at hgfin ⊢
      infer_instance
    let e : (⊤_ Scheme) ≅ Spec (CommRingCat.of (ULift ℤ)) :=
      (CategoryTheory.Limits.terminalIsTerminal :
        CategoryTheory.Limits.IsTerminal (⊤_ Scheme)).uniqueUpToIso specULiftZIsTerminal
    have hcomp :
        IsProper (CategoryTheory.Limits.terminal.from (Spec (CommRingCat.of (A 0))) ≫ e.hom) := by
      have heq : CategoryTheory.Limits.terminal.from (Spec (CommRingCat.of (A 0))) ≫ e.hom = g := by
        apply specULiftZIsTerminal.hom_ext
      rw [heq]
      exact hg
    exact (MorphismProperty.cancel_right_of_respectsIso (@IsProper)
      (CategoryTheory.Limits.terminal.from (Spec (CommRingCat.of (A 0)))) e.hom).mp hcomp
  have hProj : IsProper (Proj.toSpecZero A) := by
    haveI : Algebra.FiniteType (A 0) (MvPolynomial (Fin (n + 1)) (ULift ℤ)) := hfiniteType
    infer_instance
  have hModel : IsProper (CategoryTheory.Limits.terminal.from (standardProjectiveSpace n)) := by
    haveI : IsProper (Proj.toSpecZero A) := hProj
    haveI : IsProper (CategoryTheory.Limits.terminal.from (Spec (CommRingCat.of (A 0)))) := hSpecA0
    unfold standardProjectiveSpace
    change IsProper (CategoryTheory.Limits.terminal.from (Proj A))
    rw [← CategoryTheory.Limits.terminal.comp_from (Proj.toSpecZero A)]
    infer_instance
  haveI : IsProper (CategoryTheory.Limits.terminal.from (standardProjectiveSpace n)) := hModel
  change IsProper (CategoryTheory.Limits.pullback.fst
    (CategoryTheory.Limits.terminal.from S)
    (CategoryTheory.Limits.terminal.from (standardProjectiveSpace n)))
  infer_instance

/--
Source theorem `line-17`: if `f : X ⟶ S` is a projective morphism of schemes, then `f` is proper.

Source proof: write `f` as a closed immersion into relative projective space `ℙ^n_S` followed by
the projection `π : ℙ^n_S ⟶ S`. The projection from projective space is proper (it is of finite
type, separated, and universally closed by the valuative criterion / standard Proj results), closed
immersions are proper, and proper morphisms are stable under composition.

Note: this is the substantive content. The properness of the projection `ℙ^n_S ⟶ S` is the deep
fact and is genuinely required by the proof; the projective-space bridge here constructs `ℙ^n_S` as
`Proj` of the standard graded polynomial ring base-changed to `S`, so properness is not assumed.
-/
theorem projective_isProper {X S : Scheme} (f : X ⟶ S)
    (hf : AlgebraicGeometry.IsProjective f) : IsProper f := by
  rcases hf with ⟨n, i, hi, hif⟩
  rw [← hif]
  haveI : IsClosedImmersion i := hi
  haveI : IsProper (AlgebraicGeometry.projectiveSpaceToBase n S) :=
    projectiveSpaceToBase_isProper n S
  infer_instance
