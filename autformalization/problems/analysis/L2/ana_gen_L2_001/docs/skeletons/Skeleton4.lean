import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Filter Set
open scoped Topology

def MeromorphicAt (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (x : 𝕜) : Prop :=
  ∃ n : ℕ, AnalyticAt 𝕜 (fun z => (z - x) ^ n • f z) x

lemma AnalyticAt.meromorphicAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) : MeromorphicAt 𝕜 f x := by sorry
