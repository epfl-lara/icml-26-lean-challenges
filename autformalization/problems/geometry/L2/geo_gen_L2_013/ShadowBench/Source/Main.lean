import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Manifold Set Topology

/--
The curve from `docs/source.tex`, represented as a map into `ℝ × ℝ` for the source's
`ℝ²`: `gamma t = (t^3, 0)`.
-/
def gamma : ℝ → ℝ × ℝ := fun t => (t ^ 3, 0)

/--
Source proof: no proof is supplied in `docs/source.tex`; the intended argument is the standard
polynomial-coordinate check. Prover notes: show the first coordinate `t ↦ t^3` is smooth and the
second coordinate is constant, then combine them for the product map.
-/
theorem gamma_smooth : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ⊤ gamma := by
  rw [contMDiff_iff_contDiff]
  change ContDiff ℝ ⊤ (fun t : ℝ => (t ^ 3, (0 : ℝ)))
  fun_prop

/--
Source proof: no proof is supplied in `docs/source.tex`. Prover notes: the first projection of
`gamma t` is `t^3`; use strict monotonicity/injectivity of cubing on `ℝ` and identify the domain
topology with the subspace topology on the image.
-/
theorem gamma_is_embedding : Topology.IsEmbedding gamma := by
  have hγ : Continuous gamma := by
    change Continuous (fun t : ℝ => (t ^ (3 : ℕ), (0 : ℝ)))
    fun_prop
  have hodd : Odd (3 : ℕ) := by decide
  have hcube : Topology.IsEmbedding (fun t : ℝ => t ^ (3 : ℕ)) := by
    have hmono : StrictMono (fun t : ℝ => t ^ (3 : ℕ)) := hodd.strictMono_pow
    have hcont : Continuous (fun t : ℝ => t ^ (3 : ℕ)) := by fun_prop
    exact hmono.isEmbedding_of_ordConnected ((isPreconnected_range hcont).ordConnected)
  have hcomp : Topology.IsEmbedding (Prod.fst ∘ gamma) := by
    simpa [gamma, Function.comp_def] using hcube
  exact Topology.IsEmbedding.of_comp hγ continuous_fst hcomp

/--
Source proof: no proof is supplied in `docs/source.tex`. Prover notes: compute the derivative of
`t ↦ (t^3, 0)` at `0`; the scalar derivative of `t^3` is `3 * 0^2 = 0`, and the constant coordinate
has derivative zero, so the manifold/Frechet derivative is the zero continuous linear map.
-/
theorem gamma_mfderiv_zero : mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) gamma 0 = 0 := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ (3 : ℕ)) 0 (0 : ℝ) := by
    simpa using (hasDerivAt_pow (3 : ℕ) (0 : ℝ))
  have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 (0 : ℝ) := by
    simpa using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hderiv : HasDerivAt (fun t : ℝ => (t ^ (3 : ℕ), (0 : ℝ))) (0 : ℝ × ℝ) (0 : ℝ) :=
    hpow.prodMk hconst
  have hfderiv : HasFDerivAt gamma (0 : ℝ →L[ℝ] ℝ × ℝ) 0 := by
    change HasFDerivAt (fun t : ℝ => (t ^ (3 : ℕ), (0 : ℝ))) (0 : ℝ →L[ℝ] ℝ × ℝ) 0
    simpa using hderiv.hasFDerivAt
  exact hfderiv.hasMFDerivAt.mfderiv

/--
Source proof: no proof is supplied in `docs/source.tex`. Prover notes: a smooth embedding is an
immersion plus a topological embedding. Use `gamma_mfderiv_zero` to contradict injectivity of the
tangent map at `0`, since the source tangent space at `0` is nontrivial but the derivative is zero.
The companion declarations `gamma_smooth` and `gamma_is_embedding` formalize the other two claims of
the same source theorem.
-/
private lemma gamma_not_isImmersionAt_zero
    (h : Manifold.IsImmersionAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ⊤ gamma (0 : ℝ)) :
    False := by
  classical
  let I := modelWithCornersSelf ℝ ℝ
  let J := modelWithCornersSelf ℝ (ℝ × ℝ)
  let e := h.domChart.extend I
  let c := h.codChart.extend J
  let S : Set ℝ := e.target
  let y0 : ℝ := e 0
  have hx0 : (0 : ℝ) ∈ e.source := by
    simpa [e, I] using h.mem_domChart_source
  have hy0 : y0 ∈ S := by
    simpa [S, y0] using e.map_source hx0
  have hSopen : IsOpen S := by
    simpa [S, e, I] using h.domChart.open_target
  have hS : UniqueDiffWithinAt ℝ S y0 := hSopen.uniqueDiffWithinAt hy0
  let L : ℝ →L[ℝ] ℝ × h.complement := ContinuousLinearMap.inl ℝ ℝ h.complement
  let R : ℝ →L[ℝ] ℝ × ℝ := (h.equiv : (ℝ × h.complement) →L[ℝ] ℝ × ℝ).comp L
  have hR_ne : R ≠ 0 := by
    intro hR
    have hz : ((1 : ℝ), (0 : h.complement)) = 0 := by
      apply h.equiv.injective
      have hA := congrArg (fun A : ℝ →L[ℝ] ℝ × ℝ => A 1) hR
      simp [R, L] at hA
    have hfst := congrArg Prod.fst hz
    norm_num at hfst
  have hright :
      fderivWithin ℝ (fun y : ℝ => h.equiv (y, (0 : h.complement))) S y0 = R := by
    simpa [R, L, Function.comp_def] using (ContinuousLinearMap.fderivWithin R hS)
  have hcharts :
      fderivWithin ℝ (fun y : ℝ => c (gamma (e.symm y))) S y0 =
      fderivWithin ℝ (fun y : ℝ => h.equiv (y, (0 : h.complement))) S y0 := by
    apply fderivWithin_congr
    · intro y hy
      simpa [e, c, S, Function.comp_def] using h.writtenInCharts hy
    · simpa [e, c, S, Function.comp_def] using h.writtenInCharts hy0
  have hleft :
      fderivWithin ℝ (fun y : ℝ => c (gamma (e.symm y))) S y0 = 0 := by
    have hsymm_y0 : e.symm y0 = (0 : ℝ) := by
      simpa [e, y0] using e.left_inv hx0
    have heCD : ContMDiffOn I I ⊤ (fun y : ℝ => e.symm y) S := by
      simpa [S, e, I] using
        (contMDiffOn_extend_symm (I := I) (n := ⊤) h.domChart_mem_maximalAtlas)
    have heDiff : DifferentiableAt ℝ (fun y : ℝ => e.symm y) y0 := by
      exact (heCD.contMDiffAt (hSopen.mem_nhds hy0)).mdifferentiableAt
        (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0) |>.differentiableAt
    have hgammaDiff : DifferentiableAt ℝ gamma (e.symm y0) := by
      have hg : MDifferentiableAt I J gamma (e.symm y0) := by
        simpa [I, J] using
          (gamma_smooth.mdifferentiableAt (x := e.symm y0)
            (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0))
      exact hg.differentiableAt
    have hgammaDeriv : fderiv ℝ gamma (e.symm y0) = 0 := by
      simpa [hsymm_y0, mfderiv_eq_fderiv] using gamma_mfderiv_zero
    have hcsource : gamma (e.symm y0) ∈ c.source := by
      simpa [c, J, hsymm_y0] using h.mem_codChart_source
    have hcOpen : IsOpen c.source := by
      simpa [c, J] using h.codChart.open_source
    have hcCD : ContMDiffOn J J ⊤ (fun z : ℝ × ℝ => c z) c.source := by
      simpa [c, J] using
        (contMDiffOn_extend (I := J) (n := ⊤) h.codChart_mem_maximalAtlas)
    have hcDiff : DifferentiableAt ℝ (fun z : ℝ × ℝ => c z) (gamma (e.symm y0)) := by
      exact (hcCD.contMDiffAt (hcOpen.mem_nhds hcsource)).mdifferentiableAt
        (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0) |>.differentiableAt
    have hgeDiff : DifferentiableAt ℝ (fun y : ℝ => gamma (e.symm y)) y0 := by
      exact hgammaDiff.comp y0 heDiff
    have hcgeDiff : DifferentiableAt ℝ (fun y : ℝ => c (gamma (e.symm y))) y0 := by
      exact hcDiff.comp y0 hgeDiff
    rw [fderivWithin_eq_fderiv hS hcgeDiff]
    calc
      fderiv ℝ (fun y : ℝ => c (gamma (e.symm y))) y0
          = (fderiv ℝ (fun z : ℝ × ℝ => c z) (gamma (e.symm y0))).comp
              (fderiv ℝ (fun y : ℝ => gamma (e.symm y)) y0) := by
            simpa [Function.comp_def] using
              (fderiv_comp y0 hcDiff hgeDiff)
      _ = (fderiv ℝ (fun z : ℝ × ℝ => c z) (gamma (e.symm y0))).comp
              ((fderiv ℝ gamma (e.symm y0)).comp (fderiv ℝ (fun y : ℝ => e.symm y) y0)) := by
            have hgeDeriv :
                fderiv ℝ (fun y : ℝ => gamma (e.symm y)) y0 =
                  (fderiv ℝ gamma (e.symm y0)).comp
                    (fderiv ℝ (fun y : ℝ => e.symm y) y0) := by
              simpa [Function.comp_def] using (fderiv_comp y0 hgammaDiff heDiff)
            rw [hgeDeriv]
      _ = 0 := by
            simp [hgammaDeriv]
  exact hR_ne <| by
    calc
      R = fderivWithin ℝ (fun y : ℝ => h.equiv (y, (0 : h.complement))) S y0 := hright.symm
      _ = fderivWithin ℝ (fun y : ℝ => c (gamma (e.symm y))) S y0 := hcharts.symm
      _ = 0 := hleft

theorem gamma_not_smooth_embedding :
    ¬ Manifold.IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ⊤ gamma := by
  intro h
  rw [Manifold.isSmoothEmbedding_iff] at h
  exact gamma_not_isImmersionAt_zero (h.1.isImmersionAt (0 : ℝ))
