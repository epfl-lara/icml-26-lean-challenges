import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.CategoryTheory.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit

open CategoryTheory
open ContinuousMap
open scoped ContinuousMap

/--
Source definition `paths_homotopic` (`docs/source.tex`, lines 17-19): a topological
space is simply connected when its fundamental groupoid is equivalent to the one-object
groupoid with only the identity morphism.  In Lean, that one-object groupoid is
`CategoryTheory.Discrete Unit`.
-/
def paths_homotopic (X : Type*) [TopologicalSpace X] : Prop :=
  Nonempty (FundamentalGroupoid X ≌ Discrete Unit)

/--
Source theorem `simply_connected_iff_paths_homotopic` (`docs/source.tex`, lines 21-26).
Source proof: equivalence of the fundamental groupoid with a one-object identity groupoid
is the same as unique morphisms between any two objects; these morphisms are paths modulo
homotopy, giving path connectedness and at most one path-homotopy class between any two
points.
Prover notes: unfold `paths_homotopic`, use the fundamental-groupoid/path-homotopy-class
correspondence, and compare with Mathlib's proof of the theorem with this same name in
`Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`.
-/
theorem simply_connected_iff_paths_homotopic (X : Type*) [TopologicalSpace X] :
    paths_homotopic X ↔
      PathConnectedSpace X ∧ ∀ x y : X, Subsingleton (Path.Homotopic.Quotient x y) := by
  have huniq :
      paths_homotopic X ↔
        Nonempty X ∧ ∀ x y : X, Nonempty (Unique (Path.Homotopic.Quotient x y)) := by
    simp only [paths_homotopic, equiv_punit_iff_unique,
      FundamentalGroupoid.nonempty_iff X, and_congr_right_iff, Nonempty.forall]
    intros
    exact ⟨fun h _ _ => h _ _, fun h _ _ => h _ _⟩
  constructor
  · intro h
    have hu := huniq.mp h
    constructor
    · exact { nonempty := hu.1
              joined := fun x y => ⟨(hu.2 x y).some.default.out⟩ }
    · intro x y
      exact @Unique.instSubsingleton _ (Nonempty.some (hu.2 x y))
  · intro h
    rcases h with ⟨hpc, hsub⟩
    letI : PathConnectedSpace X := hpc
    exact huniq.mpr ⟨hpc.nonempty, fun x y => by
      letI : Subsingleton (Path.Homotopic.Quotient x y) := hsub x y
      exact ⟨uniqueOfSubsingleton ⟦PathConnectedSpace.somePath x y⟧⟩⟩
