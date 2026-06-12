import Mathlib
import Aesop

open scoped Manifold
open Set ContDiff

/--
Source theorem `line-17` (`docs/source.tex`): if `M` is a smooth manifold without
boundary, `N` is a smooth manifold with boundary, `F : M → N` is smooth, and the
manifold derivative `dF_p` is nonsingular, then `F p` lies in the manifold interior
of `N`.

Source proof: no proof is supplied in the source document. Prover notes: use local
charts around `p` and `F p`; if `F p` were a boundary point of the half-space model,
the boundary coordinate of the coordinate expression of `F` would have a local
minimum at the source point, forcing a nonzero coordinate functional to vanish on the
range of `mfderiv (𝓡 m) (𝓡∂ n) F p`, contradicting its bijectivity.
-/
theorem isInteriorPoint_of_bijective_mfderiv
    {m n : ℕ} [NeZero n]
    {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ⊤ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]
    [IsManifold (𝓡∂ n) ⊤ N]
    (F : M → N) (hF : ContMDiff (𝓡 m) (𝓡∂ n) ⊤ F)
    (p : M) (hp : Function.Bijective (mfderiv (𝓡 m) (𝓡∂ n) F p)) :
    F p ∈ (𝓡∂ n).interior N := by
  simpa [ModelWithCorners.interior] using
    (hF.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv
      hp.surjective (BoundarylessManifold.isInteriorPoint : (𝓡 m).IsInteriorPoint p)
