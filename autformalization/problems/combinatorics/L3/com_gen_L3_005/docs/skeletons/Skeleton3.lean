import Mathlib.Algebra.Notation.Indicator
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open BigOperators Finset Fintype

/-- We say that a simple graph G is bipartite with respect to sets s and t if:
  1. s and t are disjoint, and  
  2. every edge connects a vertex in s to a vertex in t (in one direction or the other) -/
def IsBipartiteWith {V : Type*} (G : SimpleGraph V) (s t : Set V) : Prop :=
  s ∩ t = ∅ ∧ ∀ u v : V, G.Adj u v → (u ∈ s ∧ v ∈ t) ∨ (u ∈ t ∧ v ∈ s)

/-- If G is a finite simple graph that is bipartite with respect to sets s and t, 
    then the sum of degrees of vertices in s equals the number of edges in G. -/
theorem isBipartiteWith_sum_degrees_eq_card_edges {V : Type*} [Fintype V] (G : SimpleGraph V) 
    (s t : Set V) (h : IsBipartiteWith G s t) : 
    ∑ v in s.toFinset, (G.degree v) = G.edges.card := by sorry
