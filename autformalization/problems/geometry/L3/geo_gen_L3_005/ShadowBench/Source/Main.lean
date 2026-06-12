import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.VectorBundle.Basic

open Bundle ContinuousMap Topology

/--
Source proof: choose the zero section as homotopy inverse to the bundle projection. The
projection after the zero section is the identity on the base, and the composite in the total
space is homotopic to the identity by fiberwise scalar multiplication `H(v,t)=t • v`.
Prover notes: construct a `ContinuousMap.HomotopyEquiv` whose forward map is `π F E` and whose
inverse is `Bundle.zeroSection F E`; prove the endpoint equations with `Bundle.zeroSection_proj`
and the vector-space identities `zero_smul` and `one_smul` after establishing continuity of the
fiberwise scaling homotopy in local trivializations.
-/
theorem proj_homotopyEquiv
    {M F : Type*} {E : M → Type*}
    [TopologicalSpace M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
    [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (Bundle.TotalSpace F E)]
    [FiberBundle F E] [VectorBundle ℝ F E] :
    ∃ h : ContinuousMap.HomotopyEquiv (Bundle.TotalSpace F E) M,
      h.toFun =
        { toFun := π F E
          continuous_toFun := FiberBundle.continuous_proj F E } := by
  classical
  have hzero : Continuous (Bundle.zeroSection F E) := by
    rw [continuous_iff_continuousAt]
    intro x0
    rw [FiberBundle.continuousAt_totalSpace]
    constructor
    · simpa [Bundle.zeroSection] using (continuousAt_id : ContinuousAt (fun x : M => x) x0)
    · let e : Trivialization F (π F E) := trivializationAt F E x0
      change ContinuousAt (fun x : M => (e (Bundle.zeroSection F E x)).2) x0
      have hconst : ContinuousAt (fun _ : M => (0 : F)) x0 := continuous_const.continuousAt
      have hbase : ∀ᶠ x in 𝓝 x0, x ∈ e.baseSet := by
        dsimp [e]
        exact (trivializationAt F E x0).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt F E x0)
      refine hconst.congr ?_
      exact hbase.mono (by
        intro x hx
        dsimp [e]
        exact (congrArg Prod.snd ((trivializationAt F E x0).zeroSection (R := ℝ) hx)).symm)
  have hsmul : Continuous (fun q : unitInterval × Bundle.TotalSpace F E =>
      (⟨q.2.proj, (q.1 : ℝ) • q.2.2⟩ : Bundle.TotalSpace F E)) := by
    rw [continuous_iff_continuousAt]
    intro q0
    rw [FiberBundle.continuousAt_totalSpace]
    constructor
    · simpa using ((FiberBundle.continuous_proj F E).continuousAt.comp
        (continuousAt_snd : ContinuousAt (fun x : unitInterval × Bundle.TotalSpace F E => x.2) q0))
    · let e : Trivialization F (π F E) := trivializationAt F E q0.2.proj
      change ContinuousAt
        (fun x : unitInterval × Bundle.TotalSpace F E =>
          (e (⟨x.2.proj, (x.1 : ℝ) • x.2.2⟩ : Bundle.TotalSpace F E)).2) q0
      have hcoord : ContinuousAt
          (fun x : unitInterval × Bundle.TotalSpace F E => (e x.2).2) q0 := by
        dsimp [e]
        exact ((FiberBundle.continuousAt_totalSpace (F := F) (E := E)
          (fun x : unitInterval × Bundle.TotalSpace F E => x.2) (x₀ := q0)).1
          (continuousAt_snd :
            ContinuousAt (fun x : unitInterval × Bundle.TotalSpace F E => x.2) q0)).2
      have hscalar : ContinuousAt
          (fun x : unitInterval × Bundle.TotalSpace F E => (x.1 : ℝ)) q0 := by
        exact continuous_subtype_val.continuousAt.comp continuousAt_fst
      have hprod : ContinuousAt
          (fun x : unitInterval × Bundle.TotalSpace F E => (x.1 : ℝ) • (e x.2).2) q0 :=
        hscalar.smul hcoord
      have hbase : ∀ᶠ x in 𝓝 q0, x.2.proj ∈ e.baseSet := by
        dsimp [e]
        exact ((FiberBundle.continuous_proj F E).continuousAt.comp
          (continuousAt_snd :
            ContinuousAt
              (fun x : unitInterval × Bundle.TotalSpace F E => x.2) q0)).eventually_mem
          ((trivializationAt F E q0.2.proj).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt F E q0.2.proj))
      refine hprod.congr ?_
      exact hbase.mono (by
        intro x hx
        dsimp [e]
        exact (((trivializationAt F E q0.2.proj).linear (R := ℝ) hx).map_smul (x.1 : ℝ) x.2.2).symm)
  let f : C(Bundle.TotalSpace F E, M) := ⟨π F E, FiberBundle.continuous_proj F E⟩
  let s : C(M, Bundle.TotalSpace F E) := ⟨Bundle.zeroSection F E, hzero⟩
  let h : ContinuousMap.HomotopyEquiv (Bundle.TotalSpace F E) M :=
    { toFun := f
      invFun := s
      left_inv := by
        let Hmap : C(unitInterval × Bundle.TotalSpace F E, Bundle.TotalSpace F E) :=
          ⟨fun q => (⟨q.2.proj, (q.1 : ℝ) • q.2.2⟩ : Bundle.TotalSpace F E), hsmul⟩
        refine ⟨{ Hmap with
          map_zero_left := ?_
          map_one_left := ?_ }⟩
        · intro x
          ext <;> simp [f, s, Hmap, Bundle.zeroSection]
        · intro x
          ext <;> simp [Hmap]
      right_inv := by
        simpa [f, s, ContinuousMap.comp, ContinuousMap.id, Bundle.zeroSection] using
          (ContinuousMap.Homotopic.refl (ContinuousMap.id M)) }
  refine ⟨h, ?_⟩
  rfl
