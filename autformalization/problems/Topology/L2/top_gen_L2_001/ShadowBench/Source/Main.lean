import Mathlib.Order.KrullDimension
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds

open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

/--
Source definition (docs/source.tex lines 17--22): the Krull dimension of a topological space is
the supremum of lengths of chains of irreducible closed subsets.  Lean represents this as the
order-theoretic Krull dimension of the poset `IrreducibleCloseds T`, with values in `WithBot ℕ∞`.
-/
noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  Order.krullDim (IrreducibleCloseds T)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/--
Source theorem (docs/source.tex lines 25--33): if `f : Y → X` is inducing, then
`dim(Y) ≤ dim(X)`.

Source proof: the source text says that preimages of chains of irreducible closed subsets of `X`
are chains in `Y`.  Prover notes: for the stated inequality, use the strict monotone map on
irreducible closed subsets induced by an inducing map, namely `map_strictMono_of_isInducing hf`,
and apply `Order.krullDim_le_of_strictMono`.
-/
theorem IsInducing.topologicalKrullDim_le {f : Y → X} (hf : IsInducing f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  sorry

/--
Source theorem (docs/source.tex lines 36--42): topological Krull dimension is invariant under
homeomorphisms.

Source proof: a homeomorphism and its inverse are inducing, so the previous theorem gives both
inequalities; conclude by antisymmetry.  Prover notes: apply
`IsInducing.topologicalKrullDim_le` to `f` and to the inverse provided by `h`, then use
`le_antisymm`.
-/
theorem IsHomeomorph.topologicalKrullDim_eq (f : X → Y) (h : IsHomeomorph f) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  sorry

/--
Source theorem (docs/source.tex lines 45--51): for any subspace `Y ⊆ X`, `dim(Y) ≤ dim(X)`.

Source proof: the inclusion of a subspace into the ambient space is inducing.  Prover notes:
instantiate `IsInducing.topologicalKrullDim_le` with the subtype inclusion and use
`IsInducing.subtypeVal`.
-/
theorem topologicalKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  sorry
