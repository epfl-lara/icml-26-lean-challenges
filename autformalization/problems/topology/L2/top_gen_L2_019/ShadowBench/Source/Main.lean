import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Perfect

open Set Topology

/--
Source theorem `line-17` (`isTotallyDisconnected_cantorSet`): the Cantor set `𝓒` is totally
disconnected and perfect.

Source proof: identify the Cantor set with the product space `ℕ → Bool`; products of discrete
two-point spaces are totally disconnected, and every cylinder neighbourhood can be altered at a
later coordinate to show no point is isolated. Closedness follows from compactness/closedness of the
Cantor set.

Prover notes: Mathlib names the ternary Cantor set `cantorSet : Set ℝ`; use the canonical
`cantorSetHomeomorphNatToBool`, `Pi.totallyDisconnectedSpace`, `isClosed_cantorSet`, and the
`Perfect` definition/accumulation-point characterization. Convert between `TotallyDisconnectedSpace
cantorSet` and `IsTotallyDisconnected cantorSet` using `totallyDisconnectedSpace_subtype_iff`.
-/
theorem isTotallyDisconnected_cantorSet :
    IsTotallyDisconnected cantorSet ∧ Perfect cantorSet := by
  have hprod : PerfectSpace (ℕ → Bool) := by
    rw [perfectSpace_iff_forall_not_isolated]
    intro f
    let y : ℕ → (ℕ → Bool) := fun n => Function.update f n (! f n)
    have hlim : Filter.Tendsto y Filter.atTop (𝓝 f) := by
      refine tendsto_pi_nhds.2 ?_
      intro i
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.Ioi_mem_atTop i] with n hn
      simp [y, Function.update_of_ne (Nat.ne_of_lt hn)]
    have hy_ne : ∀ n, y n ≠ f := by
      intro n h
      have hcoord := congrFun h n
      simp [y] at hcoord
    have hmap : Filter.map y Filter.atTop ≤ 𝓝[≠] f := by
      rw [nhdsWithin]
      refine le_inf hlim ?_
      rw [Filter.le_principal_iff, Filter.mem_map]
      exact Filter.Eventually.of_forall (fun n => by simpa using hy_ne n)
    exact (Filter.map_neBot (m := y) (hf := (inferInstance : Filter.NeBot Filter.atTop))).mono hmap
  have hperfectSubtype : PerfectSpace cantorSet := by
    rw [perfectSpace_iff_forall_not_isolated]
    intro x
    have hxProd : (𝓝[≠] (cantorSetHomeomorphNatToBool x)).NeBot :=
      (perfectSpace_iff_forall_not_isolated.mp hprod) (cantorSetHomeomorphNatToBool x)
    have hxMap : (Filter.map cantorSetHomeomorphNatToBool.symm
        (𝓝[≠] (cantorSetHomeomorphNatToBool x))).NeBot :=
      Filter.map_neBot (m := cantorSetHomeomorphNatToBool.symm) (hf := hxProd)
    simpa using hxMap
  constructor
  · have htdSubtype : TotallyDisconnectedSpace cantorSet := by
      rw [totallyDisconnectedSpace_iff]
      have h := (cantorSetHomeomorphNatToBool.symm.isEmbedding.isTotallyDisconnected_range).2
        (inferInstance : TotallyDisconnectedSpace (ℕ → Bool))
      simpa [Set.range_eq_univ] using h
    exact totallyDisconnectedSpace_subtype_iff.mp htdSubtype
  · constructor
    · exact isClosed_cantorSet
    · intro x hx
      have hxSub : (𝓝[≠] (⟨x, hx⟩ : cantorSet)).NeBot :=
        (perfectSpace_iff_forall_not_isolated.mp hperfectSubtype) ⟨x, hx⟩
      simpa [AccPt] using (nhds_ne_subtype_neBot_iff.mp hxSub)
