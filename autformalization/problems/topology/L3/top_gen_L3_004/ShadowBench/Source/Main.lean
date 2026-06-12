import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.UnitInterval

open Topology unitInterval

/--
Source proof (docs/source.tex, theorem `line-17`, proof lines 19--225): choose local
homeomorphism charts for `p`, cover the path `t ↦ g (t, a)` by chart domains, use
compactness of the unit interval to take a finite monotone subdivision, and inductively
extend a replacement lift across one subdivision interval at a time.  In the inductive
step, a tube lemma keeps `f` inside one chart range near `[tₙ,tₙ₊₁] × {a}`; shrink the
parameter neighborhood so the previous lift is in the chart source at the frontier, then
paste the old lift before `tₙ` with the inverse chart after `tₙ`.  The frontier equality
uses injectivity of the local homeomorphism chart.  Prover notes: preserve both the lift
property `p ∘ g' = f` and the agreement on `{0} × A ∪ I × {a}` throughout the induction.
-/
theorem exists_lift_nhds {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace A] {p : E → X} (hp : IsLocalHomeomorph p)
    {f : I × A → X} (hf : Continuous f) {g : I × A → E} (hg_lift : p ∘ g = f)
    (a : A) (hg_cont : ContinuousOn g ((({0} : Set I) ×ˢ Set.univ) ∪ (Set.univ ×ˢ {a}))) :
    ∃ N : Set A, IsOpen N ∧ a ∈ N ∧ ∃ g' : I × A → E,
      ContinuousOn g' (Set.univ ×ˢ N) ∧
      p ∘ g' = f ∧
      ∀ x ∈ (({0} : Set I) ×ˢ Set.univ) ∪ (Set.univ ×ˢ {a}), g' x = g x := by
  have h0 : Continuous (fun b : A => g (0, b)) := by
    simpa [Function.comp_def] using
      hg_cont.comp_continuous (Continuous.prodMk_right (0 : I)) (fun b => by
        exact Or.inl ⟨by simp, by simp⟩)
  have ha : Continuous (fun t : I => g (t, a)) := by
    simpa [Function.comp_def] using
      hg_cont.comp_continuous (Continuous.prodMk_left a) (fun t => by
        exact Or.inr ⟨by simp, by simp⟩)
  obtain ⟨N, hN, g', hg'_cont, hg'_lift, hg'_zero, hg'_a⟩ :=
    hp.exists_lift_nhds (f := ⟨f, hf⟩) (g := g) hg_lift h0 a ha
  obtain ⟨U, hUN, hUopen, haU⟩ := mem_nhds_iff.mp hN
  refine ⟨U, hUopen, haU, g', ?_, hg'_lift, ?_⟩
  · exact hg'_cont.mono (fun x hx => ⟨hx.1, hUN hx.2⟩)
  · rintro ⟨t, b⟩ (hzero | ha')
    · have ht : t = 0 := by simpa using hzero.1
      subst t
      exact hg'_zero b
    · have hb : b = a := by simpa using ha'.2
      subst b
      exact hg'_a t
