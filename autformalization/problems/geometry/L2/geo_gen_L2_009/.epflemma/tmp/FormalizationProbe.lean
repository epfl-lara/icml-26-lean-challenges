import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open scoped Manifold ContDiff

theorem tangentBundleProdDiffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    (I' : ModelWithCorners ℝ E' H')
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] :
    ∃ f : TangentBundle (I.prod I') (M × N) ≃
        (TangentBundle I M × TangentBundle I' N),
      CMDiff ∞ f ∧ CMDiff ∞ f.symm := by
  refine ⟨equivTangentBundleProd I M I' N, ?_, ?_⟩
  · exact contMDiff_equivTangentBundleProd
  · exact contMDiff_equivTangentBundleProd_symm
