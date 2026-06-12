import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UnitInterval

open scoped unitInterval Topology
open Homeomorph

/-- The coordinate-face boundary used to represent `∂ I^N` for the finite cube. -/
def cubeBoundary (N : ℕ) : Set (Fin N → unitInterval) :=
  {y | ∃ i : Fin N, y i = 0 ∨ y i = 1}

/--
The generalized `N`-loop space `Ω^N(X,x)` from `docs/source.tex`, lines 17-39.
It is represented as the subtype of bundled continuous maps `I^N → X` whose values on the
chosen coordinate-face boundary of the cube are the basepoint `x`. The topology on this type is
the inherited subtype topology from the compact-open topology on `C(Fin N → unitInterval, X)`.
-/
def setoid (X : Type*) [TopologicalSpace X] (x : X) (N : ℕ) : Type _ :=
  {f : C(Fin N → unitInterval, X) // ∀ y, y ∈ cubeBoundary N → f y = x}

namespace setoid

variable {X : Type*} [TopologicalSpace X]

/-- The inherited subtype topology from the compact-open continuous-map space. -/
instance instTopologicalSpace (x : X) (N : ℕ) : TopologicalSpace (setoid X x N) :=
  inferInstanceAs
    (TopologicalSpace
      {f : C(Fin N → unitInterval, X) // ∀ y, y ∈ cubeBoundary N → f y = x})

/-- The subtype inclusion witnessing the inherited compact-open topology representation. -/
def toContinuousMap (x : X) (N : ℕ) : setoid X x N → C(Fin N → unitInterval, X) :=
  fun f => f.1

/-- The evaluation map `(f,y) ↦ f(y)` on the generalized loop space. -/
def ev (x : X) (N : ℕ) : setoid X x N × (Fin N → unitInterval) → X :=
  fun p => (toContinuousMap x N p.1) p.2

/--
Source proof / prover notes (`docs/source.tex`, line-17): the source states that evaluation on
`Ω^N(X,x)`, with the topology inherited from the compact-open topology on continuous maps, is
continuous. There is no separate source proof. To prove this, unfold `ev`, use `toContinuousMap`
as the subtype inclusion into `C(Fin N → unitInterval, X)`, and compose the product of that
continuous inclusion with the compact-open evaluation map. The cube `Fin N → unitInterval` is a
finite product of compact locally compact spaces, so compact-open full evaluation applies.
-/
theorem continuous_ev (x : X) (N : ℕ) :
    Continuous (ev x N) := by
  have hmap : Continuous (fun p : setoid X x N × (Fin N → unitInterval) =>
      toContinuousMap x N p.1) := by
    simpa [toContinuousMap] using
      (continuous_fst.subtype_val :
        Continuous (fun p : setoid X x N × (Fin N → unitInterval) => p.1.1))
  simpa [ev] using hmap.eval continuous_snd

/--
Source proof / prover notes (`docs/source.tex`, line-17): the fixed-point evaluation statement is
the source's “in particular” clause. It follows either by composing `continuous_ev` with the
continuous map `f ↦ (f,y)`, or directly from fixed evaluation continuity for compact-open bundled
continuous maps after composing with the subtype inclusion `toContinuousMap x N`.
-/
theorem continuous_ev_at (x : X) (N : ℕ) (y : Fin N → unitInterval) :
    Continuous (fun f : setoid X x N => (toContinuousMap x N f) y) := by
  simpa [ev] using (continuous_ev x N).comp
    ((continuous_id : Continuous (fun f : setoid X x N => f)).prodMk
      (continuous_const : Continuous (fun _ : setoid X x N => y)))

end setoid
