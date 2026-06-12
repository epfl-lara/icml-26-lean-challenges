import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory

/-!
ShadowBench problem `analysis/L2/ana_gen_L2_005`.
Source theorem: `docs/source.tex`, line 17.
Blueprint: `ShadowBench/Source/Blueprint.md`.
-/

/--
Source proof: define `G x = F a + ∫ t in a..x, F' t`, show `F = G` on `[a,b]`, use
absolute continuity of interval-integral primitives together with constants and sums, then apply the
fundamental theorem of calculus on `[a,b]` for the endpoint identity.

Prover notes: this Lean statement represents the source derivative `F'` by `deriv F` and uses
`AbsolutelyContinuousOnInterval F a b` for absolute continuity on the closed interval. Try
the primitive theorem
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` and FTC lemmas from
`IntervalIntegral.FundThmCalculus`. If Mathlib's `IntervalIntegrable` is too weak to derive the
primitive equality asserted in the source proof, return to statement/source review rather than
changing this theorem during proving.
-/
theorem ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv
    {a b : ℝ} {F : ℝ → ℝ}
    (hcont : ContinuousOn F (Icc a b))
    (hab : a ≤ b)
    (hdiff : DifferentiableOn ℝ F (Ioo a b))
    (hintegr : IntervalIntegrable (deriv F) volume a b) :
    AbsolutelyContinuousOnInterval F a b ∧ F b - F a = ∫ x in a..b, deriv F x := by
  have hcont_u : ContinuousOn F (uIcc a b) := by
    simpa [uIcc_of_le hab] using hcont
  have hderiv_at : ∀ x ∈ uIoo a b, DifferentiableAt ℝ F x := by
    intro x hx
    have hx' : x ∈ Ioo a b := by
      simpa [uIoo_of_le hab] using hx
    exact (hdiff x hx').differentiableAt (Ioo_mem_nhds hx'.1 hx'.2)
  have hInt_eq : ∫ x in a..b, deriv F x = F b - F a :=
    intervalIntegral.integral_deriv_eq_sub_uIoo hcont_u hderiv_at hintegr
  have hP : AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in a..x, deriv F t) a b :=
    hintegr.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hG : AbsolutelyContinuousOnInterval (fun x ↦ F a + ∫ t in a..x, deriv F t) a b := by
    simpa [AbsolutelyContinuousOnInterval] using hP
  have hFG : ∀ x ∈ uIcc a b, F x = F a + ∫ t in a..x, deriv F t := by
    intro x hx
    have hxI : x ∈ Icc a b := by
      simpa [uIcc_of_le hab] using hx
    have hax : a ≤ x := hxI.1
    have hcont_ax : ContinuousOn F (uIcc a x) := by
      rw [uIcc_of_le hax]
      exact hcont.mono (fun y hy ↦ ⟨hy.1, le_trans hy.2 hxI.2⟩)
    have hderiv_ax : ∀ y ∈ uIoo a x, DifferentiableAt ℝ F y := by
      intro y hy
      have hy' : y ∈ Ioo a x := by
        simpa [uIoo_of_le hax] using hy
      have hyab : y ∈ Ioo a b := ⟨hy'.1, lt_of_lt_of_le hy'.2 hxI.2⟩
      exact (hdiff y hyab).differentiableAt (Ioo_mem_nhds hyab.1 hyab.2)
    have hint_ax : IntervalIntegrable (deriv F) volume a x := by
      exact hintegr.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le hax]
        intro y hy
        exact ⟨hy.1, le_trans hy.2 hxI.2⟩)
    have hix : ∫ t in a..x, deriv F t = F x - F a :=
      intervalIntegral.integral_deriv_eq_sub_uIoo hcont_ax hderiv_ax hint_ax
    linarith
  have hF_abs : AbsolutelyContinuousOnInterval F a b := by
    rw [absolutelyContinuousOnInterval_iff] at hG ⊢
    intro ε hε
    rcases hG ε hε with ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro E hE hsum
    convert hδ E hE hsum using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hleft : (E.2 i).1 ∈ uIcc a b := (hE.1 i hi).1
    have hright : (E.2 i).2 ∈ uIcc a b := (hE.1 i hi).2
    rw [hFG (E.2 i).1 hleft, hFG (E.2 i).2 hright]
  exact ⟨hF_abs, hInt_eq.symm⟩
