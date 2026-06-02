import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.NoetherianSpace

open Set TopologicalSpace Topology

theorem IsQuasiSeparated_image_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] 
  (S : Set X) (h : X → Y) (Sh : IsQuasiSeparable S) (he : IsEmbedding h) : 
  IsQuasiSeparable (h '' S) := by sorry

theorem IsQuasiSeparated.image_of_isEmbedding : True := by sorry
