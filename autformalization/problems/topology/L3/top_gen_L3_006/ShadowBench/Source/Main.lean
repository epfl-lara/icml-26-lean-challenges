import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

open Topology unitInterval

/--
Source theorem `docs/source.tex`, lines 17--63.

Source proof: choose, for each `a : A`, a path from `a₀` to `a` and a lifted path
starting at `e₀`; use endpoint uniqueness to make `F a` independent of choices.
Continuity is proved locally by a local inverse for the local homeomorphism `p` and
path-connected neighborhoods in `A`. Uniqueness follows by lifting any path from
`a₀` to `a` through both candidate maps and applying endpoint uniqueness.

Prover notes: `f`, paths, lifts, and the resulting map are encoded as mathlib
continuous maps. The assumptions `h₁` and `h₂` are exactly the source path-lifting
existence and lifted-endpoint uniqueness hypotheses over the unit interval `I`.
-/
theorem existsUnique_continuousMap_lifts {E X A : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    (p : E → X) (hp : IsLocalHomeomorph p)
    (f : C(A, X))
    (a₀ : A) (e₀ : E) (he₀ : p e₀ = f a₀)
    (h₁ : ∀ γ : C(I, A), γ 0 = a₀ →
      ∃ Γ : C(I, E), Γ 0 = e₀ ∧
        p ∘ (Γ : I → E) = (f : A → X) ∘ (γ : I → A))
    (h₂ : ∀ γ γ' : C(I, A), γ 0 = a₀ → γ' 0 = a₀ →
      ∀ Γ Γ' : C(I, E), Γ 0 = e₀ → Γ' 0 = e₀ →
        p ∘ (Γ : I → E) = (f : A → X) ∘ (γ : I → A) →
        p ∘ (Γ' : I → E) = (f : A → X) ∘ (γ' : I → A) →
        γ 1 = γ' 1 → Γ 1 = Γ' 1) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ (F : A → E) = (f : A → X) := by
  sorry
