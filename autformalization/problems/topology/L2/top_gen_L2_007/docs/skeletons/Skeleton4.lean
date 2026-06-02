import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.NoetherianSpace

open Set TopologicalSpace Topology

theorem IsQuasiSeparated.image_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsQuasiSeparated s) {f : X → Y} (hf : IsEmbedding f) :
    IsQuasiSeparated (f '' s) := by sorry
