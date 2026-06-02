import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Filter Set
open scoped Topology

variable (K : Type*) [NormedField K] [Nontrivial K] 
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]

/--
We say that $f$ is meromorphic at $x$ if there exists $n \in \mathbb{N}$ such that the function
$z \mapsto (z - x)^n f(z)$ is analytic at $x$.
-/
def MeromorphicAt (f : K → E) (x : K) : Prop :=
  ∃ n : ℕ, AnalyticAt K (fun z => (z - x) ^ n • f z) x

/--
If $f$ is analytic at $x$, then $f$ is meromorphic at $x$.
-/
theorem AnalyticAt.meromorphicAt (f : K → E) (x : K) (h : AnalyticAt K f x) : 
  MeromorphicAt f x := by sorry
