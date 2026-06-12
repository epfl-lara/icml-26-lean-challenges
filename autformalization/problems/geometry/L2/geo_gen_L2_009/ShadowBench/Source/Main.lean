import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open scoped Manifold ContDiff

/--
Source: `docs/source.tex`, theorem block `line-17` (`tangentBundleProdDiffeomorph`).

Source proof: the LaTeX source supplies no proof beyond the statement.
Proof sketch: use the canonical Mathlib equivalence `equivTangentBundleProd I M I' N`,
which identifies a tangent vector over `(x, y)` with the pair of tangent vectors over
`x` and `y`.  Its forward and inverse smoothness are provided by
`contMDiff_equivTangentBundleProd` and `contMDiff_equivTangentBundleProd_symm`.
Prover notes: the source phrase "diffeomorphic" is encoded as an equivalence together
with `CMDiff ∞` for both directions; real smooth manifolds are represented by
`IsManifold I ∞` and `IsManifold I' ∞`.
-/
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
