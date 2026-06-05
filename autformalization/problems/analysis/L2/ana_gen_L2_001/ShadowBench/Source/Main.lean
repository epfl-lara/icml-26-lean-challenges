import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Filter Set
open scoped Topology

/--
Source `docs/source.tex`, line-17 (`MeromorphicAt`). A function `f : 𝕜 → E` is
meromorphic at `x` if some natural power of `z - x`, acting by scalar multiplication
on `f z`, makes the resulting function analytic at `x`.
-/
def MeromorphicAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : 𝕜 → E) (x : 𝕜) : Prop :=
  ∃ n : ℕ, AnalyticAt 𝕜 (fun z => (z - x) ^ n • f z) x

/--
Source `docs/source.tex`, line-24 (`AnalyticAt.meromorphicAt`).
Source proof: choose the witness `n = 0`; then `(z - x)^0 • f z = f z`, so the
analyticity required by `MeromorphicAt` is exactly the hypothesis.
Prover notes: unfold `MeromorphicAt`, refine `⟨0, ?_⟩`, and simplify with
`pow_zero` and `one_smul` using `hf`.
-/
lemma AnalyticAt.meromorphicAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    MeromorphicAt f x := by
  sorry
