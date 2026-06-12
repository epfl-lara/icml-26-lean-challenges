import Mathlib.Geometry.Manifold.MFDeriv.Tangent

open scoped Manifold Topology
open Set

/-!
# ShadowBench geometry/L2/geo_diff_L2_002

This file formalizes the source lemma from `docs/source.tex`.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
`IsMIntegralCurveOn Γ v U` means that `Γ : ℝ → M` is an integral curve of the
vector field `v` at every time in `U`, using manifold derivatives within `U`.
This is the local definition needed to state the source lemma.
-/
def IsMIntegralCurveOn (Γ : ℝ → M) (v : (x : M) → TangentSpace I x) (U : Set ℝ) : Prop :=
  ∀ t ∈ U, HasMFDerivAt[U] Γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (Γ t))

/--
`IsMIntegralCurveAt Γ v t₀` means that the integral-curve derivative relation
holds eventually in the neighborhood filter of `t₀`.
-/
def IsMIntegralCurveAt (Γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasMFDerivAt% Γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (Γ t))

/--
Source lemma `line-17` / `isMIntegralCurveAt_iff'` from `docs/source.tex`:
`Γ : ℝ → M` is an integral curve of `v` at `t₀` iff there exists an open
neighborhood `U` of `t₀` such that `Γ` is an integral curve of `v` on `U`.

Source proof: no proof is provided in the source document.
Proof sketch / prover notes: unfold `IsMIntegralCurveAt` as an eventual
neighborhood property. Forward, choose an open set inside the eventual
neighborhood using `mem_nhds_iff`, and restrict point derivatives to
within-`U` derivatives. Reverse, use `IsOpen.mem_nhds` to make `U` an eventual
neighborhood, then turn the within-`U` derivative into a point derivative at
each `t ∈ U`.
-/
theorem isMIntegralCurveAt_iff'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {Γ : ℝ → M} {v : (x : M) → TangentSpace I x} {t₀ : ℝ} :
    IsMIntegralCurveAt Γ v t₀ ↔
      ∃ U : Set ℝ, IsOpen U ∧ t₀ ∈ U ∧ IsMIntegralCurveOn Γ v U := by
  constructor
  · intro h
    rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at h
    obtain ⟨s, hs, hderiv⟩ := h
    obtain ⟨U, hUsub, hUopen, ht₀U⟩ := mem_nhds_iff.mp hs
    refine ⟨U, hUopen, ht₀U, ?_⟩
    intro t htU
    exact (hderiv t (hUsub htU)).hasMFDerivWithinAt
  · rintro ⟨U, hUopen, ht₀U, hUcurve⟩
    rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem]
    refine ⟨U, hUopen.mem_nhds ht₀U, ?_⟩
    intro t htU
    exact (hUcurve t htU).hasMFDerivAt (hUopen.mem_nhds htU)
