import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open SimpleGraph Finset

variable {n t : ℕ} [NeZero t]
def Edge n:= Sym2 (Fin n)

open SimpleGraph Std

def SimpleGraph.IsSpannerOf (H G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  H.IsSubgraph G ∧ ∀ u v : Fin n, H.edist u v ≤ t * G.edist u v

open Classical in
noncomputable def SimpleGraph.numEdges (G : SimpleGraph (Fin n)) : ℕ := #G.edgeFinset
