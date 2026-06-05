import Mathlib

open scoped Manifold ContDiff

/-- Source theorem `global_integralCurve_unique_fundamental_period` from `docs/source.tex`,
lines 17--19.
Source proof: the source document states the exercise without a proof.
Proof sketch: let the period set be the additive subgroup of all shifts `s` with
`∀ t, γ (t + s) = γ t`. Periodicity makes it nontrivial. For a smooth vector field,
uniqueness of global integral curves makes every self-intersection `γ t = γ t'`
produce the period `t - t'`. If the period subgroup were dense, continuity would force
`γ` to be constant, contradicting the nonconstant hypothesis; hence the subgroup is cyclic
with least positive generator `T`. Then self-intersections are exactly integer multiples of
`T`, and the least-positive-generator characterization gives uniqueness.
Prover notes: use Mathlib's manifold integral-curve API (`IsMIntegralCurve.periodic_of_eq`,
`IsMIntegralCurve.continuous`) and the ordered-additive-subgroup dichotomy for subgroups of
`ℝ` (for example `AddSubgroup.dense_xor'_addCyclic` / `Subgroup.dense_or_cyclic`). The smooth
vector field `X ∈ 𝔛(M)` is represented by a dependent tangent-space section plus the
`CMDiff ∞` hypothesis below. -/
theorem global_integralCurve_unique_fundamental_period
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SecondCountableTopology M]
    (X : (x : M) → TangentSpace I x)
    (hX_smooth : CMDiff ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (γ : ℝ → M)
    (hγ_global : IsMIntegralCurve γ X)
    (hγ_periodic : ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, γ (t + T) = γ t)
    (hγ_nonconstant : ¬ ∃ x : M, ∀ t : ℝ, γ t = x) :
    ∃! T : ℝ, 0 < T ∧
      ∀ t t' : ℝ, γ t = γ t' ↔ ∃ k : ℤ, t - t' = (k : ℝ) * T := by
  sorry
