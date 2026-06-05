import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homotopy.Lifting

open Topology unitInterval

/--
Source `docs/source.tex`, lines 17-67 (`liftPath_zero`; exported as `exists_path_lifts`).
Source proof: cover the image of the path by evenly covered neighborhoods, subdivide `I`,
and continue the lift sheet-by-sheet from the chosen point over `γ 0`.
Prover notes: this statement uses continuous maps `C(I, ·)` for source paths; Mathlib's
`IsCoveringMap.exists_path_lifts` has this exact shape.
-/
theorem exists_path_lifts {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {γ : C(I, X)} {e : E} (he : γ 0 = p e) :
    ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e := by
  sorry

/--
Source `docs/source.tex`, lines 70-151 (`eq_liftPath_iff`).
Source proof: for `S = {x | g₁ x = g₂ x}`, use evenly covered neighborhoods to show `S`
is open and closed; since the domain is preconnected and the maps agree at `a`, conclude
`S = univ` and hence `g₁ = g₂`.
Prover notes: `g₁` and `g₂` are encoded as continuous maps, and the witness of nonempty
agreement is passed as `(a, ha)`. Mathlib's `IsCoveringMap.eq_of_comp_eq` packages the
same uniqueness-of-lifts argument.
-/
lemma eq_liftPath_iff {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace A] {f : E → X} (hf : IsCoveringMap f) [PreconnectedSpace A]
    {g₁ g₂ : C(A, E)} (hfg : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) :
    g₁ = g₂ := by
  sorry

/--
Source `docs/source.tex`, lines 153-207 (`eq_liftPath_iff'`).
Source proof: equality with the chosen lift immediately gives continuity, lifting, and the
initial value. Conversely, any continuous lift of `γ` starting at `e` agrees with the chosen
lift by uniqueness of lifts on the connected interval.
Prover notes: the source's chosen lift `γ̃` is represented by Mathlib's `hp.liftPath γ e he`;
`hp.eq_liftPath_iff` is essentially this characterization.
-/
lemma eq_liftPath_iff' {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {γ : C(I, X)} {e : E} (he : γ 0 = p e)
    (Γ : I → E) :
    Γ = hp.liftPath γ e he ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e := by
  sorry
