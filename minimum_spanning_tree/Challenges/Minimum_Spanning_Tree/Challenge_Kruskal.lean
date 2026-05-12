/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isabel Haas, Pratyai Mazumder, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Challenges.Minimum_Spanning_Tree.Def_UnionFindN
import Challenges.Minimum_Spanning_Tree.Def_WeightedGraph

open WeightedGraph

set_option tactic.hygienic false

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

abbrev UnionFind (n: ℕ) := UnionFindStructure n
abbrev UnionFind.empty {n : ℕ} : UnionFind n := @UnionFindStructure.make n
abbrev UnionFind.find {n : ℕ} (uf : UnionFind n) (x : Fin n) : Fin n := @UnionFindStructure.find n uf x
abbrev UnionFind.union {n : ℕ} (uf : UnionFind n) (x y : Fin n) : UnionFind n := @UnionFindStructure.union n uf x y

-- === Kruskal algorithm ===
-- kruskalAux function
noncomputable def kruskalAux  {n : ℕ}
  (G : WeightedGraph (Fin n))
  (edgeList : List (Sym2 (Fin n)))
  (uf : UnionFind n)
  (forest : Finset (Sym2 (Fin n)))
  :
  Finset (Sym2 (Fin n)) × UnionFind n :=
  match edgeList with
  | [] => (forest, uf)
  | e::es =>
    let u := e.out.1
    let v := e.out.2
    if uf.find u ≠ uf.find v then
      let newforest := {e} ∪ forest -- add edge to forest
      let newuf := uf.union u v -- put u v into the same component
      kruskalAux G es newuf newforest -- recursive call
    else
      kruskalAux G es uf forest -- recursive call
  termination_by edgeList.length decreasing_by
    all_goals exact Nat.lt_add_one es.length

-- If forest and edges are both subsets of the graph's edges,
-- then kruskalAux returns a subset of the graph's eddges
lemma returns_edge_subset {n: ℕ} {G : WeightedGraph (Fin n)}
  {es : List (Sym2 (Fin n))}
  {uf : UnionFind n} {forest : Finset (Sym2 (Fin n))}
  (hf: forest ⊆ G.edgeFinset)
  (hes: es.toFinset ⊆ G.edgeFinset):
  (kruskalAux G es uf forest).1 ⊆ G.edgeFinset := by
  fun_induction kruskalAux
  . exact hf
  . apply ih1
    . dsimp [newforest]
      rw [Finset.insert_subset_iff]
      constructor
      . rw [List.toFinset_cons] at hes
        rw [Finset.insert_subset_iff] at hes
        exact hes.1
      . exact hf
    . exact subsetList hes
  . apply ih1
    . exact hf
    . exact subsetList hes

--- == Kruskal's algorithm ==
noncomputable def kruskal {n : ℕ} (G: WeightedGraph (Fin n)):
  WeightedGraph (Fin n) :=
  let es := Finset.sort (G.edgeFinset) G.byWeight
  let uf := @UnionFind.empty n
  let forest := ∅
  have hes : es.toFinset ⊆ G.edgeFinset := by
    rw [Finset.sort_toFinset]
  let resaux := kruskalAux G es uf forest
  have hks: resaux.1 ⊆ G.edgeFinset := by
    dsimp [resaux, forest]
    apply returns_edge_subset
    exact Finset.empty_subset G.edgeFinset
    exact hes
  G.FromEdgeSubset resaux.1 hks

-- CORRECTNESS PROOF : Kruskal Algorithm computes MST
theorem kruskal_computes_MST {n : ℕ} (G: WeightedGraph (Fin n)) (hn: n > 0)
  (hG: G.Connected):
  (kruskal G).IsMST G := sorry
