import Mathlib.Geometry.Manifold.MFDeriv.Tangent

open scoped Manifold Topology
open Set

namespace ShadowBench.Source

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
Source-local spelling of “`Γ` is an integral curve of `v` on `U`”.
It matches the manifold-derivative representation of Mathlib's integral-curve-on
predicate while avoiding a name collision with Mathlib's theorem
`isMIntegralCurveAt_iff'`.
-/
def IsMIntegralCurveOn (Γ : ℝ → M) (v : (x : M) → TangentSpace I x) (U : Set ℝ) : Prop :=
  ∀ t ∈ U, HasMFDerivAt[U] Γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (Γ t))

/--
Source-local spelling of “`Γ` is an integral curve of `v` at `t₀`”.
It requires the manifold-derivative equation eventually in the neighborhood
filter of `t₀`.
-/
def IsMIntegralCurveAt (Γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasMFDerivAt% Γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (Γ t))

end ShadowBench.Source

/--
Source lemma `line-17`, `isMIntegralCurveAt_iff'`:
Let `M` be a manifold and `v` be a vector field on `M`. Then a curve
`Γ : ℝ → M` is an integral curve of `v` at `t₀` iff there exists an open
neighborhood `U` of `t₀` such that `Γ` is an integral curve of `v` on `U`.

Source proof: no proof is included in `docs/source.tex`.
Proof sketch: unfold the source-local `IsMIntegralCurveAt` and
`IsMIntegralCurveOn`; the claim is the neighborhood-filter characterization
`Filter.eventually_iff_exists_mem` plus `mem_nhds_iff`, using open sets
containing `t₀` as neighborhood witnesses.
Prover notes: Mathlib has analogous predicates and facts in
`Mathlib.Geometry.Manifold.IntegralCurve.Basic`, especially
`isMIntegralCurveAt_iff`; those are search hints rather than direct imports here
because that module already declares a theorem named `isMIntegralCurveAt_iff'`.
-/
theorem isMIntegralCurveAt_iff'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (Γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) :
    ShadowBench.Source.IsMIntegralCurveAt Γ v t₀ ↔
      ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ ShadowBench.Source.IsMIntegralCurveOn Γ v U := by
  sorry
