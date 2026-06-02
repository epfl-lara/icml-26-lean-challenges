import Mathlib
import Mathlib.Manifold.SmoothManifold
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic

open scoped Manifold ContDiff

theorem exists_smooth_vectorField_on_graph {M N : Type*} 
  [TopologicalSpace M] [TopologicalSpace N]
  [SmoothManifoldWithBoundary M] [SmoothManifold N] 
  (f : M → N) (hf : ContDiff ℝ ⊤ f) :
  let F : M → M × N := fun x => (x, f x)
  ∀ (X : M → tangentBundle M), 
    (∀ p : M, ContDiff ℝ ⊤ (fun t => X t)) → -- X is smooth
    ∃ (Y : (M × N) → tangentBundle (M × N)), 
      (∀ q : M × N, ContDiff ℝ ⊤ (fun t => Y t)) ∧ -- Y is smooth
      ∀ p : M, fderiv ℝ F p (X p) = Y (F p) := by sorry
