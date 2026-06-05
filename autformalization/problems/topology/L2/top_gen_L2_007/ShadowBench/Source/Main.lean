import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.NoetherianSpace

open Set TopologicalSpace Topology

/-- A subset of a topological space is quasi-separated when the intersection of any two compact
open subsets contained in it is compact. This records the set-level object class used by the source
statement. -/
def IsQuasiSeparated {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∀ U V : Set X,
    U ⊆ s → IsOpen U → IsCompact U →
    V ⊆ s → IsOpen V → IsCompact V →
    IsCompact (U ∩ V)

/--
Source proof: for compact open subsets `U,V` of the image, pull them back along the
embedding. The preimages are compact open subsets of `s`, so their intersection is compact by
quasi-separatedness of `s`. Push this compact intersection forward and identify it with `U ∩ V`
using injectivity and the fact that `U,V` lie in the range of the image.

Prover notes: unfold `IsQuasiSeparated`; use preimages `f ⁻¹' U` and `f ⁻¹' V`, `hf.continuous`,
`hf.isCompact_iff`, `hf.injective`, `Set.preimage_inter`, and `Set.image_preimage_eq_inter_range`.
The source writes the embedding as `h` but the image as `f(S)`; the Lean statement uses one map `f`.
-/
theorem IsQuasiSeparated.image_of_isEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {s : Set X} {f : X → Y} (hs : IsQuasiSeparated s)
    (hf : IsEmbedding f) : IsQuasiSeparated (f '' s) := by
  sorry
