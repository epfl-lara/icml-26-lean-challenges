import Mathlib.Combinatorics.SimpleGraph.Bipartite

open BigOperators Finset Fintype

/-- Source definition `docs/source.tex` lines 17--25.  `G` is bipartite with respect to
sets `s` and `t` when the two sets are disjoint and every edge has one endpoint in each set.
This source-level declaration is a transparent wrapper around Mathlib's exact predicate
`SimpleGraph.IsBipartiteWith`. -/
def IsBipartiteWith {V : Type*} (G : SimpleGraph V) (s t : Set V) : Prop :=
  G.IsBipartiteWith s t

/-- Source theorem `docs/source.tex` lines 27--39.

Source proof: each edge of a bipartite graph has exactly one endpoint in `s` and the
other endpoint in `t`; summing degrees over `s` counts every edge exactly once, by its
unique endpoint in `s`.

Prover notes: unfold the wrapper `IsBipartiteWith`, identify the finite source subset `s`
with `s.toFinset`, and use Mathlib's bipartite degree-sum theorem
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges`. -/
theorem isBipartiteWith_sum_degrees_eq_card_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Set V)
    [DecidablePred (fun v => v ∈ s)] (h : IsBipartiteWith G s t) :
    ∑ v ∈ s.toFinset, G.degree v = G.edgeFinset.card := by
  classical
  simpa [IsBipartiteWith] using
    (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges (G := G)
      (s := s.toFinset) (t := t.toFinset) (by simpa [IsBipartiteWith] using h))
