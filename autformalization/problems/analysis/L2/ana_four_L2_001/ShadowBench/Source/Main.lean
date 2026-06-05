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

/--
Source definition (docs/source.tex, lines 17--28): the Fourier transform associated to a
measure `μ`, bilinear form `L`, and additive character `e` sends `f : V → E` to the
function of `w : W` given by the displayed Bochner integral.  The source product
bilinear form is represented by the curried linear map `V →ₗ[K] W →ₗ[K] K`, and the
source unit circle `𝕊` by Mathlib's `Circle`, coerced to `ℂ` for scalar multiplication.
-/
noncomputable def fourierIntegral {K V W E : Type*} [CommRing K]
    [MeasurableSpace V] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (μ : Measure V) (L : V →ₗ[K] W →ₗ[K] K)
    (e : AddChar K Circle) (f : V → E) : W → E :=
  fun w ↦ ∫ v, ((e (-L v w) : Circle) : ℂ) • f v ∂μ

/--
Source proof (docs/source.tex, lines 36--51): evaluate both functions at an arbitrary `w`.
The integrand for `r • f` is `e(-L(v,w)) • (r • f v)`, then linearity of the
Bochner integral pulls the constant scalar `r : ℂ` outside, yielding
`r • fourierIntegral μ L e f w`.
Prover notes: use function extensionality in `w`; unfold `fourierIntegral`; commute the two
complex scalar multiplications in the integrand; apply `MeasureTheory.integral_smul`.
-/
theorem fourierIntegral_const_smul {K V W E : Type*} [CommRing K]
    [MeasurableSpace V] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (μ : Measure V) (L : V →ₗ[K] W →ₗ[K] K)
    (e : AddChar K Circle) (f : V → E) (r : ℂ) :
    fourierIntegral μ L e (r • f) = r • fourierIntegral μ L e f := by
  sorry
