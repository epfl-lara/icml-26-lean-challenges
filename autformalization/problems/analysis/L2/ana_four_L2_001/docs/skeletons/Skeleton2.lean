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

-- Definition of Fourier integral
noncomputable def fourierIntegral {K V W E : Type*} [CommRing K] [AddCommGroup V] [Module K V] 
  [AddCommGroup W] [Module K W] [NormedAddCommGroup E] [NormedSpace ℂ E] 
  [CompleteSpace E] (μ : Measure V) (L : V × W → K) (e : AddChar K) (f : V → E) :
  W → E := fun w => ∫ v, e (-L (v, w)) • f v ∂μ

-- Theorem about scalar multiplication property
theorem fourierIntegral_const_smul {K V W E : Type*} [CommRing K] [AddCommGroup V] [Module K V] 
  [AddCommGroup W] [Module K W] [NormedAddCommGroup E] [NormedSpace ℂ E] 
  [CompleteSpace E] (μ : Measure V) (L : V × W → K) (e : AddChar K) (f : V → E) 
  (r : ℂ) : 
  fourierIntegral μ L e (fun v => r • f v) = fun w => r • fourierIntegral μ L e f w := by sorry
