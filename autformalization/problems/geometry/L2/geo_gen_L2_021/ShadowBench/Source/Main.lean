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
  classical
  have h_one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := by norm_num
  haveI : IsManifold I 1 M := IsManifold.of_le h_one_le_infty
  let P : AddSubgroup ℝ :=
    { carrier := {s : ℝ | Function.Periodic γ s}
      zero_mem' := Function.periodic_with_period_zero γ
      add_mem' := by
        intro a b ha hb
        exact ha.add_period hb
      neg_mem' := by
        intro a ha
        exact ha.neg }
  have hX_one : CMDiff 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) := hX_smooth.of_le h_one_le_infty
  have hself_period : ∀ t t' : ℝ, γ t = γ t' ↔ t - t' ∈ P := by
    intro t t'
    constructor
    · intro heq
      exact hγ_global.periodic_of_eq hX_one heq
    · intro hp
      have hper : Function.Periodic γ (t - t') := hp
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hper t'
  have int_mul_ge_of_pos :
      ∀ {T x : ℝ} (hT : 0 < T) (hx : 0 < x) {k : ℤ},
        x = (k : ℝ) * T → T ≤ x := by
    intro T x hT hx k hk
    have hmulpos : 0 < (k : ℝ) * T := by
      simpa [hk] using hx
    have hmulpos' : 0 < T * (k : ℝ) := by
      simpa [mul_comm] using hmulpos
    have hkR : 0 < (k : ℝ) := pos_of_mul_pos_right hmulpos' hT.le
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hkR
    have hk1Z : (1 : ℤ) ≤ k := by omega
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1Z
    calc
      T = (1 : ℝ) * T := by ring
      _ ≤ (k : ℝ) * T := mul_le_mul_of_nonneg_right hk1R hT.le
      _ = x := hk.symm
  rcases AddSubgroup.dense_or_cyclic P with hP_dense | hP_cyclic
  · exfalso
    apply hγ_nonconstant
    refine ⟨γ 0, fun t ↦ ?_⟩
    exact hP_dense.induction
      (fun s hs ↦ by simpa using hs 0)
      (isClosed_eq hγ_global.continuous continuous_const) t
  · rcases hP_cyclic with ⟨a, hPclosure⟩
    have hP : P = AddSubgroup.zmultiples a := by
      simpa [← AddSubgroup.zmultiples_eq_closure] using hPclosure
    obtain ⟨T₀, hT₀pos, hT₀per⟩ := hγ_periodic
    have hT₀P : T₀ ∈ P := hT₀per
    have hT₀z : T₀ ∈ AddSubgroup.zmultiples a := by
      simpa [hP] using hT₀P
    rcases AddSubgroup.mem_zmultiples_iff.mp hT₀z with ⟨k₀, hk₀⟩
    have ha_ne : a ≠ 0 := by
      intro ha
      subst a
      simp at hk₀
      linarith
    have hTpos : 0 < |a| := abs_pos.mpr ha_ne
    have h_abs : AddSubgroup.zmultiples |a| = AddSubgroup.zmultiples a := by
      by_cases ha_nonneg : 0 ≤ a
      · rw [abs_of_nonneg ha_nonneg]
      · have ha_neg : a < 0 := lt_of_not_ge ha_nonneg
        rw [abs_of_neg ha_neg]
        ext x
        constructor
        · intro hx
          rcases AddSubgroup.mem_zmultiples_iff.mp hx with ⟨k, hk⟩
          rw [AddSubgroup.mem_zmultiples_iff]
          refine ⟨-k, ?_⟩
          simpa [zsmul_neg, neg_zsmul] using hk
        · intro hx
          rcases AddSubgroup.mem_zmultiples_iff.mp hx with ⟨k, hk⟩
          rw [AddSubgroup.mem_zmultiples_iff]
          refine ⟨-k, ?_⟩
          simpa [zsmul_neg, neg_zsmul] using hk
    have hPabs : P = AddSubgroup.zmultiples |a| := hP.trans h_abs.symm
    have hmem_T : ∀ x : ℝ, x ∈ P ↔ ∃ k : ℤ, x = (k : ℝ) * |a| := by
      intro x
      constructor
      · intro hx
        have hxz : x ∈ AddSubgroup.zmultiples |a| := by
          simpa [hPabs] using hx
        rcases AddSubgroup.mem_zmultiples_iff.mp hxz with ⟨k, hk⟩
        exact ⟨k, by simpa [zsmul_eq_mul] using hk.symm⟩
      · rintro ⟨k, hk⟩
        have hxz : x ∈ AddSubgroup.zmultiples |a| := by
          rw [AddSubgroup.mem_zmultiples_iff]
          refine ⟨k, ?_⟩
          simpa [zsmul_eq_mul] using hk.symm
        simpa [hPabs] using hxz
    refine ⟨|a|, ⟨hTpos, ?_⟩, ?_⟩
    · intro t t'
      exact (hself_period t t').trans (hmem_T (t - t'))
    · intro T' hT'
      rcases hT' with ⟨hT'pos, hprop'⟩
      apply le_antisymm
      · have hTmem : |a| ∈ P := by
          rw [hPabs]
          exact AddSubgroup.mem_zmultiples |a|
        have hperT : Function.Periodic γ |a| := hTmem
        have hEqT : γ |a| = γ 0 := by
          simpa using hperT 0
        obtain ⟨k, hk⟩ := (hprop' |a| 0).mp hEqT
        have hk' : |a| = (k : ℝ) * T' := by simpa using hk
        exact int_mul_ge_of_pos hT'pos hTpos hk'
      · have hEqT' : γ T' = γ 0 := by
          apply (hprop' T' 0).mpr
          refine ⟨1, by ring⟩
        have hT'P : T' ∈ P := by
          have hp := (hself_period T' 0).mp hEqT'
          simpa using hp
        obtain ⟨k, hk⟩ := (hmem_T T').mp hT'P
        exact int_mul_ge_of_pos hTpos hT'pos hk
