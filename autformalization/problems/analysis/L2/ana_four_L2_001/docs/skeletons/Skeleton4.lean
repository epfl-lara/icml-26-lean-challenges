import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Filter
open scoped Topology

noncomputable def fourierIntegral {K V W E : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure V) (L : V →ₗ[K] W →ₗ[K] K) (e : AddChar K Circle) (f : V → E) : W → E :=
  fun w ↦ ∫ v, (e (-L v w) : ℂ) • f v ∂μ

theorem fourierIntegral_const_smul {K V W E : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure V) (L : V →ₗ[K] W →ₗ[K] K) (e : AddChar K Circle) (f : V → E) (r : ℂ) :
    fourierIntegral μ L e (r • f) = r • fourierIntegral μ L e f := by sorry
