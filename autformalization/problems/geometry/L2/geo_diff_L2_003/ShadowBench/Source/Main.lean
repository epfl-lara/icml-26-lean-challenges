import Mathlib.Geometry.Manifold.MFDeriv.Tangent

open scoped Manifold Topology
open Set

/--
`Γ` is an integral curve of the vector field `v` on the time set `s`: at every
`t ∈ s`, the manifold derivative within `s` sends `1 : ℝ` to `v (Γ t)`.
This is the representation bridge for the source phrase “integral curve on `U`”.
-/
def IsMIntegralCurveOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (Γ : ℝ → M) (v : (x : M) → TangentSpace I x) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasMFDerivAt[s] Γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (Γ t))

/--
`Γ` is an integral curve of the vector field `v` at `t₀`: in a neighborhood of
`t₀`, the manifold derivative sends `1 : ℝ` to `v (Γ t)`.
This is the representation bridge for the source phrase “integral curve at `t₀`”.
-/
def IsMIntegralCurveAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (Γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasMFDerivAt% Γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (Γ t))

/--
Source proof: The source gives no proof. The statement unfolds the definition of
`IsMIntegralCurveAt` as an eventual property at `t₀`; an open neighborhood carrying
that eventual property gives the right-hand side, and conversely `IsOpen U` with
`t₀ ∈ U` means `U ∈ 𝓝 t₀`, so the integral-curve-on-`U` hypothesis supplies the
eventual derivative condition.

Prover notes: unfold `IsMIntegralCurveAt` and `IsMIntegralCurveOn`; use
`Filter.eventually_iff_exists_mem`, `mem_nhds_iff`, and `IsOpen.mem_nhds`, plus the
standard conversions between `HasMFDerivAt` and `HasMFDerivWithinAt` on a
neighborhood.
-/
theorem isMIntegralCurveAt_iff'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x} {Γ : ℝ → M} {t₀ : ℝ} :
    IsMIntegralCurveAt Γ v t₀ ↔
      ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ IsMIntegralCurveOn Γ v U := by
  constructor
  · intro h
    rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at h
    obtain ⟨s, hs, h⟩ := h
    obtain ⟨U, hUs, hUopen, ht₀U⟩ := mem_nhds_iff.mp hs
    refine ⟨U, hUopen, ht₀U, ?_⟩
    intro t ht
    exact (h t (hUs ht)).hasMFDerivWithinAt
  · rintro ⟨U, hUopen, ht₀U, hU⟩
    rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem]
    refine ⟨U, hUopen.mem_nhds ht₀U, ?_⟩
    intro t ht
    exact (hU t ht).hasMFDerivAt (hUopen.mem_nhds ht)
