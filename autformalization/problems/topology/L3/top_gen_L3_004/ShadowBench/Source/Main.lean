import Mathlib.Topology.Covering.Basic
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
  sorry
