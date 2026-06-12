import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.UnitInterval

open Topology unitInterval

/--
Source theorem `monodromy_theorem` from `docs/source.tex`, lines 18-40.
Source proof: define `G(s,t) = Γ t s`; Theorem B gives continuity of `G` from the
continuous lifted slices, the constant initial side, and the projected homotopy. The
projected endpoint path `t ↦ p (Γ t 1)` is constant because `γ` is a homotopy rel.
endpoints. Separatedness/uniqueness of lifts for `p` then forces the endpoint lift
`t ↦ Γ t 1` to be constant, giving `Γ t 1 = Γ 0 1`.
Prover notes: the Lean draft makes the source proof's implicit separated/unique-lift
assumption explicit as `hp : IsCoveringMap p`. Search `Path.Homotopy.target` and
covering-map lifting uniqueness lemmas such as `IsCoveringMap.liftHomotopy` or
`IsCoveringMap.existsUnique_continuousMap_lifts`.
-/
theorem monodromy_theorem {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (p : E → X) (hp : IsCoveringMap p)
    {x y : X}
    (γ₀ γ₁ : Path x y)
    (γ : Path.Homotopy γ₀ γ₁)
    (Γ : I → C(I, E))
    (hΓ : ∀ t s, p (Γ t s) = γ (t, s))
    (hΓ₀ : ∀ t, Γ t 0 = Γ 0 0) :
    ∀ t, Γ t 1 = Γ 0 1 := by
  intro t
  exact IsLocalHomeomorph.monodromy_theorem hp.isLocalHomeomorph hp.isSeparatedMap γ Γ hΓ hΓ₀ t
