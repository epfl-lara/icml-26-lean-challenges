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

-- Helper lemma: FromEdgeSubset creates a subgraph
lemma FromEdgeSubset_IsSubgraph {sG : WeightedGraph V} {s : Finset (Sym2 V)}
  (hset : s ⊆ sG.edgeFinset) :
  (sG.FromEdgeSubset s hset).IsSubgraph sG := by
  constructor
  · exact SimpleGraph.from_edge_subset_is_subgraph sG s hset
  · intro u v huv
    have h_adj : (SimpleGraph.fromEdgeSet s).Adj u v := huv
    dsimp [FromEdgeSubset]
    rw [if_pos h_adj]

-- Helper lemma: Kruskal output is a subgraph of G
lemma kruskal_IsSubgraph {n : ℕ} (G : WeightedGraph (Fin n)) :
  (kruskal G).IsSubgraph G := by
  unfold kruskal
  apply FromEdgeSubset_IsSubgraph

-- === Lemmas about Forest.graft and find ===

lemma graft_find_same {n : ℕ} (f : Forest n) (x root : Fin n)
    (h_root : f.isRoot root)
    (h_neq : x ≠ root) :
    UnionFindStructure.find (f.graft x root h_root h_neq) x = root := by
  let f' := f.graft x root h_root h_neq
  have h1 : f'.parent.get x = some root := by
    dsimp [f', Forest.graft]
    exact ArrayN.get_set_eq f.parent x (some root)
  have h2 : f'.parent.get root = none := by
    dsimp [f', Forest.graft]
    rw [ArrayN.get_set_ne f.parent x root (some root) h_neq]
    exact h_root
  have h3 : UnionFindStructure.find f' x = UnionFindStructure.find f' root := by
    rw [find_eq]
    rw [h1]
  have h4 : UnionFindStructure.find f' root = root := by
    rw [find_eq]
    rw [h2]
  rw [h3, h4]

lemma graft_find_other {n : ℕ} (f : Forest n) (x root : Fin n)
    (h_root : f.isRoot root)
    (h_neq : x ≠ root)
    (h_x_root : f.isRoot x)
    (z : Fin n)
    (h_z : UnionFindStructure.find f z ≠ x) :
    let f' := f.graft x root h_root h_neq
    UnionFindStructure.find f' z = UnionFindStructure.find f z := by
  let f' := f.graft x root h_root h_neq
  have h_z_ne_x : z ≠ x := by
    by_contra h
    subst z
    have : UnionFindStructure.find f x = x := by
      rw [find_eq]
      rw [show f.parent.get x = none by exact h_x_root]
    contradiction
  have h_ind := Forest.induction f (P := fun k => UnionFindStructure.find f k ≠ x → UnionFindStructure.find f' k = UnionFindStructure.find f k)
    (fun a h_a_root h_a => by
      have h_a_ne_x : a ≠ x := by
        by_contra h
        subst a
        have : UnionFindStructure.find f x = x := by
          rw [find_eq]
          rw [show f.parent.get x = none by exact h_x_root]
        contradiction
      rw [find_eq, find_eq]
      have h1 : f'.parent.get a = f.parent.get a := by
        dsimp [f', Forest.graft]
        apply ArrayN.get_set_ne
        exact Ne.symm h_a_ne_x
      rw [h1, h_a_root])
    (fun a p h_parent ih h_a => by
      have h_a_ne_x : a ≠ x := by
        by_contra h
        subst a
        have : f.parent.get x = none := by exact h_x_root
        rw [this] at h_parent
        contradiction
      have h_p : UnionFindStructure.find f p ≠ x := by
        have : UnionFindStructure.find f a = UnionFindStructure.find f p := by
          rw [find_eq]
          rw [h_parent]
        rw [this] at h_a
        exact h_a
      rw [find_eq, find_eq]
      have h1 : f'.parent.get a = f.parent.get a := by
        dsimp [f', Forest.graft]
        apply ArrayN.get_set_ne
        exact Ne.symm h_a_ne_x
      rw [h1, h_parent]
      exact ih h_p)
    z
  exact h_ind h_z

lemma graft_find_merged {n : ℕ} (f : Forest n) (x root : Fin n)
    (h_root : f.isRoot root)
    (h_neq : x ≠ root)
    (h_x_root : f.isRoot x)
    (z : Fin n)
    (h_z : UnionFindStructure.find f z = x) :
    let f' := f.graft x root h_root h_neq
    UnionFindStructure.find f' z = root := by
  let f' := f.graft x root h_root h_neq
  have h_ind := Forest.induction f (P := fun k => UnionFindStructure.find f k = x → UnionFindStructure.find f' k = root)
    (fun a h_a_root h_a => by
      have h_a_eq_x : a = x := by
        rw [find_eq] at h_a
        rw [show f.parent.get a = none by exact h_a_root] at h_a
        exact h_a
      rw [h_a_eq_x]
      exact graft_find_same f x root h_root h_neq)
    (fun a p h_parent ih h_a => by
      have h_a_ne_x : a ≠ x := by
        by_contra h
        subst a
        have : f.parent.get x = none := by exact h_x_root
        rw [this] at h_parent
        contradiction
      have h_p : UnionFindStructure.find f p = x := by
        rw [find_eq] at h_a
        rw [h_parent] at h_a
        exact h_a
      rw [find_eq]
      have h1 : f'.parent.get a = f.parent.get a := by
        dsimp [f', Forest.graft]
        apply ArrayN.get_set_ne
        exact Ne.symm h_a_ne_x
      rw [h1, h_parent]
      exact ih h_p)
    z
  exact h_ind h_z

-- === Lemmas about UnionFind.union and find ===

lemma union_find_same {n : ℕ} (s : UnionFindStructure n) (x y : Fin n) :
    let s' := s.union x y
    s'.find x = s'.find y := by
  rw [UnionFindStructure.union]
  split_ifs with h
  . exact h
  . let root_x := s.find x
    let root_y := s.find y
    have h_rx : s.isRoot root_x := find_returns_root s x
    have h_ry : s.isRoot root_y := find_returns_root s y
    rw [UnionFindStructure.union_roots]
    split_ifs with h1 h2
    . -- graft root_x to root_y
      let s' := s.graft root_x root_y h_ry h
      have h_find_x : s.find x = root_x := rfl
      have h_find_y : s.find y = root_y := rfl
      have h_x : UnionFindStructure.find s' x = root_y := by
        apply graft_find_merged s root_x root_y h_ry h h_rx x
        exact h_find_x
      have h_y : UnionFindStructure.find s' y = root_y := by
        apply graft_find_other s root_x root_y h_ry h h_rx y
        rw [h_find_y]
        exact Ne.symm h
      change UnionFindStructure.find s' x = UnionFindStructure.find s' y
      rw [h_x, h_y]
    . -- graft root_y to root_x
      let s' := s.graft root_y root_x h_rx (Ne.symm h)
      have h_find_x : s.find x = root_x := rfl
      have h_find_y : s.find y = root_y := rfl
      have h_x : UnionFindStructure.find s' x = root_x := by
        apply graft_find_other s root_y root_x h_rx (Ne.symm h) h_ry x
        rw [h_find_x]
        exact h
      have h_y : UnionFindStructure.find s' y = root_x := by
        apply graft_find_merged s root_y root_x h_rx (Ne.symm h) h_ry y
        exact h_find_y
      change UnionFindStructure.find s' x = UnionFindStructure.find s' y
      rw [h_x, h_y]
    . -- graft root_y to root_x (equal rank)
      let s' := s.graft root_y root_x h_rx (Ne.symm h)
      have h_find_x : s.find x = root_x := rfl
      have h_find_y : s.find y = root_y := rfl
      have h_x : UnionFindStructure.find s' x = root_x := by
        apply graft_find_other s root_y root_x h_rx (Ne.symm h) h_ry x
        rw [h_find_x]
        exact h
      have h_y : UnionFindStructure.find s' y = root_x := by
        apply graft_find_merged s root_y root_x h_rx (Ne.symm h) h_ry y
        exact h_find_y
      change UnionFindStructure.find s' x = UnionFindStructure.find s' y
      rw [h_x, h_y]

lemma union_find_preserve {n : ℕ} (s : UnionFindStructure n) (x y z : Fin n)
    (h_x : s.find z ≠ s.find x)
    (h_y : s.find z ≠ s.find y) :
    let s' := s.union x y
    s'.find z = s.find z := by
  rw [UnionFindStructure.union]
  split_ifs with h
  . rfl
  . let root_x := s.find x
    let root_y := s.find y
    have h_rx : s.isRoot root_x := find_returns_root s x
    have h_ry : s.isRoot root_y := find_returns_root s y
    rw [UnionFindStructure.union_roots]
    split_ifs with h1 h2
    . -- graft root_x to root_y
      let s' := s.graft root_x root_y h_ry h
      apply graft_find_other s root_x root_y h_ry h h_rx z
      exact h_x
    . -- graft root_y to root_x
      let s' := s.graft root_y root_x h_rx (Ne.symm h)
      apply graft_find_other s root_y root_x h_rx (Ne.symm h) h_ry z
      exact h_y
    . -- graft root_y to root_x (equal rank)
      let s' := s.graft root_y root_x h_rx (Ne.symm h)
      apply graft_find_other s root_y root_x h_rx (Ne.symm h) h_ry z
      exact h_y

lemma union_find_merged_x {n : ℕ} (s : UnionFindStructure n) (x y z : Fin n)
    (h_z : s.find z = s.find x) :
    let s' := s.union x y
    s'.find z = s'.find x := by
  rw [UnionFindStructure.union]
  split_ifs with h
  . exact h_z
  . let root_x := s.find x
    let root_y := s.find y
    have h_rx : s.isRoot root_x := find_returns_root s x
    have h_ry : s.isRoot root_y := find_returns_root s y
    rw [UnionFindStructure.union_roots]
    split_ifs with h1 h2
    . -- graft root_x to root_y
      let s' := s.graft root_x root_y h_ry h
      have h_z' : UnionFindStructure.find s' z = root_y := by
        apply graft_find_merged s root_x root_y h_ry h h_rx z
        exact h_z
      have h_x' : UnionFindStructure.find s' x = root_y := by
        apply graft_find_merged s root_x root_y h_ry h h_rx x
        rfl
      change UnionFindStructure.find s' z = UnionFindStructure.find s' x
      rw [h_z', h_x']
    . -- graft root_y to root_x
      let s' := s.graft root_y root_x h_rx (Ne.symm h)
      have h_z' : UnionFindStructure.find s' z = s.find z := by
        apply graft_find_other s root_y root_x h_rx (Ne.symm h) h_ry z
        intro h_eq
        apply h
        rw [←h_z]
        exact h_eq
      have h_x' : UnionFindStructure.find s' x = s.find x := by
        apply graft_find_other s root_y root_x h_rx (Ne.symm h) h_ry x
        exact h
      change UnionFindStructure.find s' z = UnionFindStructure.find s' x
      rw [h_z', h_x']
      exact h_z
    . -- graft root_y to root_x (equal rank)
      let s' := s.graft root_y root_x h_rx (Ne.symm h)
      have h_z' : UnionFindStructure.find s' z = s.find z := by
        apply graft_find_other s root_y root_x h_rx (Ne.symm h) h_ry z
        intro h_eq
        apply h
        rw [←h_z]
        exact h_eq
      have h_x' : UnionFindStructure.find s' x = s.find x := by
        apply graft_find_other s root_y root_x h_rx (Ne.symm h) h_ry x
        exact h
      change UnionFindStructure.find s' z = UnionFindStructure.find s' x
      rw [h_z', h_x']
      exact h_z

lemma union_find_merged_y {n : ℕ} (s : UnionFindStructure n) (x y z : Fin n)
    (h_z : s.find z = s.find y) :
    let s' := s.union x y
    s'.find z = s'.find y := by
  rw [UnionFindStructure.union]
  split_ifs with h
  . -- find x = find y
    exact h_z
  . let root_x := s.find x
    let root_y := s.find y
    have h_rx : s.isRoot root_x := find_returns_root s x
    have h_ry : s.isRoot root_y := find_returns_root s y
    rw [UnionFindStructure.union_roots]
    split_ifs with h1 h2
    . -- graft root_x to root_y
      let s' := s.graft root_x root_y h_ry h
      have h_z' : UnionFindStructure.find s' z = root_y := by
        have h1 : UnionFindStructure.find s' z = s.find z := by
          apply graft_find_other s root_x root_y h_ry h h_rx z
          intro h_eq
          apply h
          rw [←h_z]
          exact h_eq.symm
        rw [h1, h_z]
      have h_y' : UnionFindStructure.find s' y = root_y := by
        have h1 : UnionFindStructure.find s' y = s.find y := by
          apply graft_find_other s root_x root_y h_ry h h_rx y
          exact Ne.symm h
        rw [h1]
      change UnionFindStructure.find s' z = UnionFindStructure.find s' y
      rw [h_z', h_y']
    . -- graft root_y to root_x
      let s' := s.graft root_y root_x h_rx (Ne.symm h)
      have h_z' : UnionFindStructure.find s' z = root_x := by
        apply graft_find_merged s root_y root_x h_rx (Ne.symm h) h_ry z
        exact h_z
      have h_y' : UnionFindStructure.find s' y = root_x := by
        apply graft_find_merged s root_y root_x h_rx (Ne.symm h) h_ry y
        rfl
      change UnionFindStructure.find s' z = UnionFindStructure.find s' y
      rw [h_z', h_y']
    . -- graft root_y to root_x (equal rank)
      let s' := s.graft root_y root_x h_rx (Ne.symm h)
      have h_z' : UnionFindStructure.find s' z = root_x := by
        apply graft_find_merged s root_y root_x h_rx (Ne.symm h) h_ry z
        exact h_z
      have h_y' : UnionFindStructure.find s' y = root_x := by
        apply graft_find_merged s root_y root_x h_rx (Ne.symm h) h_ry y
        rfl
      change UnionFindStructure.find s' z = UnionFindStructure.find s' y
      rw [h_z', h_y']

lemma union_find_eq_preserve {n : ℕ} (s : UnionFindStructure n) (x y u v : Fin n)
    (h_eq : s.find x = s.find y) :
    let s' := s.union u v
    s'.find x = s'.find y := by
  intro s'
  by_cases h_xu : s.find x = s.find u
  . have h1 : s'.find x = s'.find u := union_find_merged_x s u v x h_xu
    have h_yu : s.find y = s.find u := by rw [←h_eq]; exact h_xu
    have h2 : s'.find y = s'.find u := union_find_merged_x s u v y h_yu
    rw [h1, h2]
  . by_cases h_xv : s.find x = s.find v
    . have h1 : s'.find x = s'.find v := union_find_merged_y s u v x h_xv
      have h_yv : s.find y = s.find v := by rw [←h_eq]; exact h_xv
      have h2 : s'.find y = s'.find v := union_find_merged_y s u v y h_yv
      rw [h1, h2]
    . have h_xu' : s.find x ≠ s.find u := by
        intro h
        apply h_xu
        exact h
      have h_xv' : s.find x ≠ s.find v := by
        intro h
        apply h_xv
        exact h
      have h1 : s'.find x = s.find x := union_find_preserve s u v x h_xu' h_xv'
      have h_yu' : s.find y ≠ s.find u := by
        rw [←h_eq]
        exact h_xu'
      have h_yv' : s.find y ≠ s.find v := by
        rw [←h_eq]
        exact h_xv'
      have h2 : s'.find y = s.find y := union_find_preserve s u v y h_yu' h_yv'
      rw [h1, h2, h_eq]

-- === Invariant preservation ===

lemma preserve_inv_add_edge {n : ℕ} (uf : UnionFind n) (forest : Finset (Sym2 (Fin n)))
  (e : Sym2 (Fin n)) (u v : Fin n)
  (he : e = s(u, v))
  (h_diff : uf.find u ≠ uf.find v)
  (hinv : ∀ x y, (SimpleGraph.fromEdgeSet forest).Reachable x y → uf.find x = uf.find y) :
  ∀ x y, (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable x y → (uf.union u v).find x = (uf.union u v).find y := by
  intro x y h_reach
  rw [SimpleGraph.reachable_eq_reflTransGen] at h_reach
  induction h_reach with
  | refl => rfl
  | @tail b c h_reach h_adj ih =>
    have h_eq1 : (uf.union u v).find x = (uf.union u v).find b := ih
    have h_eq2 : (uf.union u v).find b = (uf.union u v).find c := by
      have h_adj' : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Adj b c := h_adj
      simp [SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff] at h_adj'
      rcases h_adj' with ⟨h_mem, h_neq⟩
      rcases h_mem with h_mem | h_mem
      . -- s(b, c) = e = s(u, v)
        rw [he] at h_mem
        have h_bc : s(b, c) = s(u, v) := h_mem
        have h_eq' : (b = u ∧ c = v) ∨ (b = v ∧ c = u) := by
          simp [Sym2.eq_iff] at h_bc
          tauto
        cases h_eq' with
        | inl h_eq1 =>
          have hb : b = u := h_eq1.1
          have hc : c = v := h_eq1.2
          rw [hb, hc]
          exact union_find_same uf u v
        | inr h_eq2 =>
          have hb : b = v := h_eq2.1
          have hc : c = u := h_eq2.2
          rw [hb, hc]
          exact (union_find_same uf u v).symm
      . -- s(b, c) ∈ forest
        have h_adj_old : (SimpleGraph.fromEdgeSet forest).Adj b c := by
          simp [SimpleGraph.fromEdgeSet, h_mem, h_neq]
        have h_reach_old : (SimpleGraph.fromEdgeSet forest).Reachable b c := by
          apply SimpleGraph.Adj.reachable h_adj_old
        have h_find_eq : uf.find b = uf.find c := hinv b c h_reach_old
        exact union_find_eq_preserve uf b c u v h_find_eq
    rw [h_eq1, h_eq2]

lemma kruskalAux_maintain_inv {n: ℕ} {G : WeightedGraph (Fin n)}
  {es : List (Sym2 (Fin n))}
  {uf : UnionFind n} {forest : Finset (Sym2 (Fin n))}
  (hf: forest ⊆ G.edgeFinset)
  (hes: es.toFinset ⊆ G.edgeFinset)
  (hinv : ∀ u v, (SimpleGraph.fromEdgeSet forest).Reachable u v → uf.find u = uf.find v) :
  ∀ u v, (SimpleGraph.fromEdgeSet (kruskalAux G es uf forest).1).Reachable u v →
    (kruskalAux G es uf forest).2.find u = (kruskalAux G es uf forest).2.find v := by
  fun_induction kruskalAux
  . exact hinv
  . -- add edge case
    apply ih1
    . dsimp [newforest]
      rw [Finset.insert_subset_iff]
      constructor
      . rw [List.toFinset_cons] at hes
        rw [Finset.insert_subset_iff] at hes
        exact hes.1
      . exact hf
    . exact subsetList hes
    . have he : e = s(u, v) := (Quot.out_eq e).symm
      intro x y h_reach
      have h' : (SimpleGraph.fromEdgeSet ({e} ∪ ↑forest_1)).Reachable x y := by
        simpa [newforest] using h_reach
      exact preserve_inv_add_edge uf_1 forest_1 e u v he h hinv x y h'
  . -- skip edge case
    apply ih1
    . exact hf
    . exact subsetList hes
    . exact hinv

lemma FromEdgeSubset_IsAcyclic_eq {n : ℕ} {G : WeightedGraph (Fin n)} {s : Finset (Sym2 (Fin n))}
  (h : s ⊆ G.edgeFinset) :
  (G.FromEdgeSubset s h).IsAcyclic = SimpleGraph.IsAcyclic (SimpleGraph.fromEdgeSet (s : Set (Sym2 (Fin n)))) := by
  simp [IsAcyclic, FromEdgeSubset]

lemma kruskalAux_IsAcyclic {n: ℕ} {G : WeightedGraph (Fin n)}
  {es : List (Sym2 (Fin n))}
  {uf : UnionFind n} {forest : Finset (Sym2 (Fin n))}
  (hf: forest ⊆ G.edgeFinset)
  (hes: es.toFinset ⊆ G.edgeFinset)
  (hacyc : (G.FromEdgeSubset forest hf).IsAcyclic)
  (hinv : ∀ u v, (SimpleGraph.fromEdgeSet forest).Reachable u v → uf.find u = uf.find v) :
  (G.FromEdgeSubset (kruskalAux G es uf forest).1 (returns_edge_subset hf hes)).IsAcyclic := by
  rw [FromEdgeSubset_IsAcyclic_eq]
  fun_induction kruskalAux
  case case1 =>
    simp
    rw [←FromEdgeSubset_IsAcyclic_eq]
    exact hacyc
  case case2 =>
    refine ih1 ?_ ?_ ?_ ?_
    . -- Show newforest ⊆ edgeFinset
      simp [newforest]
      rw [Finset.insert_subset_iff]
      constructor
      . rw [List.toFinset_cons] at hes
        rw [Finset.insert_subset_iff] at hes
        exact hes.1
      . exact hf
    . exact subsetList hes
    . -- Show the new graph is acyclic
      have he : e = s(u, v) := (Quot.out_eq e).symm
      have h_not_reach : ¬(SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable u v := by
        by_contra h_reach
        have : uf_1.find u = uf_1.find v := hinv u v h_reach
        contradiction
      have h1 : (SimpleGraph.fromEdgeSet (↑newforest : Set (Sym2 (Fin n)))).IsAcyclic ↔
        (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).IsAcyclic := by
        have h_eq : SimpleGraph.fromEdgeSet (↑newforest : Set (Sym2 (Fin n))) =
          SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n))) ⊔ SimpleGraph.fromEdgeSet {e} := by
          simp [newforest]
          ext a b
          simp [SimpleGraph.fromEdgeSet]
          tauto
        rw [h_eq, he]
        apply SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable
        exact h_not_reach
      exact h1.mpr hacyc
    . -- Show the invariant is preserved
      have he : e = s(u, v) := (Quot.out_eq e).symm
      intro x y h_reach
      have h' : (SimpleGraph.fromEdgeSet ({e} ∪ (forest_1 : Set (Sym2 (Fin n))))).Reachable x y := by
        simpa [newforest] using h_reach
      exact preserve_inv_add_edge uf_1 forest_1 e u v he h hinv x y h'
  case case3 =>
    refine ih1 ?_ ?_ ?_ ?_
    . exact hf
    . exact subsetList hes
    . exact hacyc
    . exact hinv

-- Helper lemma: Kruskal output is acyclic
lemma kruskal_IsAcyclic {n : ℕ} (G : WeightedGraph (Fin n)) :
  (kruskal G).IsAcyclic := by
  unfold kruskal IsAcyclic
  dsimp [WeightedGraph.toSimpleGraph]
  apply kruskalAux_IsAcyclic
  case hf => exact Finset.empty_subset G.edgeFinset
  case hes => rw [Finset.sort_toFinset]
  case hacyc =>
    rw [FromEdgeSubset_IsAcyclic_eq]
    simp [SimpleGraph.isAcyclic_bot]
  case hinv =>
    intro u v h_reach
    have h_eq : u = v := by
      simp [Finset.coe_empty, SimpleGraph.fromEdgeSet_empty] at h_reach
      exact h_reach
    rw [h_eq]

-- Helper lemma: forest only grows in kruskalAux
lemma kruskalAux_forest_mono {n: ℕ} {G : WeightedGraph (Fin n)}
  {es : List (Sym2 (Fin n))}
  {uf : UnionFind n} {forest : Finset (Sym2 (Fin n))} :
  forest ⊆ (kruskalAux G es uf forest).1 := by
  fun_induction kruskalAux
  case case1 => exact Finset.Subset.refl _
  case case2 =>
    have h_insert : {e} ∪ forest_1 ⊆ (kruskalAux G es_1 (uf_1.union u v) ({e} ∪ forest_1)).1 := ih1
    have h_sub : forest_1 ⊆ {e} ∪ forest_1 := Finset.subset_insert _ _
    exact Finset.Subset.trans h_sub h_insert
  case case3 => exact ih1

-- Helper lemma: reachability is preserved when adding edges
lemma reachable_mono {n : ℕ} {s t : Set (Sym2 (Fin n))} (h : s ⊆ t) {a b : Fin n}
  (h_reach : (SimpleGraph.fromEdgeSet s).Reachable a b) :
  (SimpleGraph.fromEdgeSet t).Reachable a b := by
  apply SimpleGraph.Reachable.mono _ h_reach
  apply SimpleGraph.fromEdgeSet_mono
  exact h

-- Helper lemma: after union, find u is either old find u or old find v
lemma union_find_u_cases {n : ℕ} (uf : UnionFind n) (u v : Fin n)
  (h_diff : uf.find u ≠ uf.find v) :
  (uf.union u v).find u = uf.find u ∨ (uf.union u v).find u = uf.find v := by
  simp only [UnionFind.union, UnionFindStructure.union]
  split_ifs with h
  · contradiction
  · rw [UnionFindStructure.union_roots]
    split_ifs with h1 h2
    · -- graft find u to find v
      let s' := uf.graft (uf.find u) (uf.find v) (find_returns_root uf v) h
      have h_eq : UnionFindStructure.find s' u = uf.find v := by
        apply graft_find_merged uf (uf.find u) (uf.find v) (find_returns_root uf v) h (find_returns_root uf u) u
        rfl
      right
      exact h_eq
    · -- graft find v to find u
      let s' := uf.graft (uf.find v) (uf.find u) (find_returns_root uf u) (Ne.symm h)
      have h_eq : UnionFindStructure.find s' u = uf.find u := by
        apply graft_find_other uf (uf.find v) (uf.find u) (find_returns_root uf u) (Ne.symm h) (find_returns_root uf v) u
        exact h_diff
      left
      exact h_eq
    · -- equal rank
      let s' := uf.graft (uf.find v) (uf.find u) (find_returns_root uf u) (Ne.symm h)
      have h_eq : UnionFindStructure.find s' u = uf.find u := by
        apply graft_find_other uf (uf.find v) (uf.find u) (find_returns_root uf u) (Ne.symm h) (find_returns_root uf v) u
        exact h_diff
      left
      exact h_eq

-- Helper lemma: sync invariant is preserved when adding an edge
lemma sync_preserve_add_edge {n : ℕ} (uf : UnionFind n) (forest : Finset (Sym2 (Fin n)))
  (e : Sym2 (Fin n)) (u v : Fin n)
  (he : e = s(u, v))
  (h_diff : uf.find u ≠ uf.find v)
  (hsync : ∀ a b, uf.find a = uf.find b → (SimpleGraph.fromEdgeSet forest).Reachable a b) :
  ∀ a b, (uf.union u v).find a = (uf.union u v).find b →
    (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable a b := by
  intro a b h_eq
  by_cases h_au : uf.find a = uf.find u
  · have h1 : (uf.union u v).find a = (uf.union u v).find u := union_find_merged_x uf u v a h_au
    by_cases h_bu : uf.find b = uf.find u
    · have h2 : (uf.union u v).find b = (uf.union u v).find u := union_find_merged_x uf u v b h_bu
      rw [h1, h2] at h_eq
      have h_reach_a_u : (SimpleGraph.fromEdgeSet forest).Reachable a u := hsync a u h_au
      have h_reach_b_u : (SimpleGraph.fromEdgeSet forest).Reachable b u := hsync b u h_bu
      have h_reach_a_b : (SimpleGraph.fromEdgeSet forest).Reachable a b :=
        h_reach_a_u.trans h_reach_b_u.symm
      exact reachable_mono (by simp) h_reach_a_b
    · by_cases h_bv : uf.find b = uf.find v
      · have h2 : (uf.union u v).find b = (uf.union u v).find v := union_find_merged_y uf u v b h_bv
        rw [h1] at h_eq
        rw [h2] at h_eq
        have h_reach_a_u : (SimpleGraph.fromEdgeSet forest).Reachable a u := hsync a u h_au
        have h_reach_b_v : (SimpleGraph.fromEdgeSet forest).Reachable b v := hsync b v h_bv
        have h_uv_adj : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Adj u v := by
          simp [SimpleGraph.fromEdgeSet_adj, he]
          intro h_eq_uv
          rw [h_eq_uv] at h_diff
          contradiction
        have h_reach_u_v : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable u v :=
          SimpleGraph.Adj.reachable h_uv_adj
        have h_reach_a_b : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable a b := by
          have h1 : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable a u :=
            reachable_mono (by simp) h_reach_a_u
          have h2 : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable v b :=
            reachable_mono (by simp) h_reach_b_v.symm
          exact h1.trans (h_reach_u_v.trans h2)
        exact h_reach_a_b
      · have h_bu' : uf.find b ≠ uf.find u := by intro h; apply h_bu; exact h
        have h_bv' : uf.find b ≠ uf.find v := by intro h; apply h_bv; exact h
        have h2 : (uf.union u v).find b = uf.find b := union_find_preserve uf u v b h_bu' h_bv'
        rw [h1] at h_eq
        rw [h2] at h_eq
        cases union_find_u_cases uf u v h_diff with
        | inl h_u =>
          rw [h_u] at h_eq
          have h_eq' : uf.find b = uf.find u := h_eq.symm
          have h_false : False := h_bu' h_eq'
          cases h_false
        | inr h_u =>
          rw [h_u] at h_eq
          have h_eq' : uf.find b = uf.find v := h_eq.symm
          have h_false : False := h_bv' h_eq'
          cases h_false
  · by_cases h_av : uf.find a = uf.find v
    · have h1 : (uf.union u v).find a = (uf.union u v).find v := union_find_merged_y uf u v a h_av
      by_cases h_bu : uf.find b = uf.find u
      · have h2 : (uf.union u v).find b = (uf.union u v).find u := union_find_merged_x uf u v b h_bu
        rw [h1] at h_eq
        rw [h2] at h_eq
        have h_reach_a_v : (SimpleGraph.fromEdgeSet forest).Reachable a v := hsync a v h_av
        have h_reach_b_u : (SimpleGraph.fromEdgeSet forest).Reachable b u := hsync b u h_bu
        have h_uv_adj : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Adj u v := by
          simp [SimpleGraph.fromEdgeSet_adj, he]
          intro h_eq_uv
          rw [h_eq_uv] at h_diff
          contradiction
        have h_reach_u_v : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable u v :=
          SimpleGraph.Adj.reachable h_uv_adj
        have h_reach_a_b : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable a b := by
          have h1 : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable a v :=
            reachable_mono (by simp) h_reach_a_v
          have h2 : (SimpleGraph.fromEdgeSet ({e} ∪ forest)).Reachable u b :=
            reachable_mono (by simp) h_reach_b_u.symm
          exact h1.trans (h_reach_u_v.symm.trans h2)
        exact h_reach_a_b
      · by_cases h_bv : uf.find b = uf.find v
        · have h2 : (uf.union u v).find b = (uf.union u v).find v := union_find_merged_y uf u v b h_bv
          rw [h1, h2] at h_eq
          have h_reach_a_v : (SimpleGraph.fromEdgeSet forest).Reachable a v := hsync a v h_av
          have h_reach_b_v : (SimpleGraph.fromEdgeSet forest).Reachable b v := hsync b v h_bv
          have h_reach_a_b : (SimpleGraph.fromEdgeSet forest).Reachable a b :=
            h_reach_a_v.trans h_reach_b_v.symm
          exact reachable_mono (by simp) h_reach_a_b
        · have h_bu' : uf.find b ≠ uf.find u := by intro h; apply h_bu; exact h
          have h_bv' : uf.find b ≠ uf.find v := by intro h; apply h_bv; exact h
          have h2 : (uf.union u v).find b = uf.find b := union_find_preserve uf u v b h_bu' h_bv'
          rw [h1] at h_eq
          rw [h2] at h_eq
          have h_v_eq_u : (uf.union u v).find v = (uf.union u v).find u := (union_find_same uf u v).symm
          cases union_find_u_cases uf u v h_diff with
          | inl h_u =>
            have h_v_eq_u' : (uf.union u v).find v = uf.find u := by
              rw [h_v_eq_u, h_u]
            rw [h_v_eq_u'] at h_eq
            have h_false : False := h_bu' h_eq.symm
            cases h_false
          | inr h_u =>
            have h_v_eq_v : (uf.union u v).find v = uf.find v := by
              rw [h_v_eq_u, h_u]
            rw [h_v_eq_v] at h_eq
            have h_false : False := h_bv' h_eq.symm
            cases h_false
    · have h_au' : uf.find a ≠ uf.find u := by intro h; apply h_au; exact h
      have h_av' : uf.find a ≠ uf.find v := by intro h; apply h_av; exact h
      have h1 : (uf.union u v).find a = uf.find a := union_find_preserve uf u v a h_au' h_av'
      by_cases h_bu : uf.find b = uf.find u
      · have h2 : (uf.union u v).find b = (uf.union u v).find u := union_find_merged_x uf u v b h_bu
        rw [h1] at h_eq
        rw [h2] at h_eq
        cases union_find_u_cases uf u v h_diff with
        | inl h_u =>
          rw [h_u] at h_eq
          have h_false : False := h_au' h_eq
          cases h_false
        | inr h_u =>
          rw [h_u] at h_eq
          have h_false : False := h_av' h_eq
          cases h_false
      · by_cases h_bv : uf.find b = uf.find v
        · have h2 : (uf.union u v).find b = (uf.union u v).find v := union_find_merged_y uf u v b h_bv
          rw [h1] at h_eq
          rw [h2] at h_eq
          have h_v_eq_u : (uf.union u v).find v = (uf.union u v).find u := (union_find_same uf u v).symm
          cases union_find_u_cases uf u v h_diff with
          | inl h_u =>
            have h_v_eq_u' : (uf.union u v).find v = uf.find u := by
              rw [h_v_eq_u, h_u]
            rw [h_v_eq_u'] at h_eq
            have h_false : False := h_au' h_eq
            cases h_false
          | inr h_u =>
            have h_v_eq_v : (uf.union u v).find v = uf.find v := by
              rw [h_v_eq_u, h_u]
            rw [h_v_eq_v] at h_eq
            have h_false : False := h_av' h_eq
            cases h_false
        · have h_bu' : uf.find b ≠ uf.find u := by intro h; apply h_bu; exact h
          have h_bv' : uf.find b ≠ uf.find v := by intro h; apply h_bv; exact h
          have h2 : (uf.union u v).find b = uf.find b := union_find_preserve uf u v b h_bu' h_bv'
          rw [h1, h2] at h_eq
          have h_reach_a_b : (SimpleGraph.fromEdgeSet forest).Reachable a b := hsync a b h_eq
          exact reachable_mono (by simp) h_reach_a_b

-- Helper lemma: if two vertices have the same find, they still have the same find after kruskalAux
lemma find_eq_preserved {n : ℕ} {G : WeightedGraph (Fin n)}
  {es : List (Sym2 (Fin n))}
  {uf : UnionFind n} {forest : Finset (Sym2 (Fin n))}
  (a b : Fin n)
  (h : uf.find a = uf.find b) :
  (kruskalAux G es uf forest).2.find a = (kruskalAux G es uf forest).2.find b := by
  fun_induction kruskalAux
  case case1 => exact h
  case case2 =>
    have h' : (uf_1.union u v).find a = (uf_1.union u v).find b :=
      union_find_eq_preserve uf_1 a b u v h
    exact ih1 h'
  case case3 => exact ih1 h

-- Helper lemma: sync invariant holds for kruskalAux final state
lemma kruskalAux_sync {n: ℕ} {G : WeightedGraph (Fin n)}
  {es : List (Sym2 (Fin n))}
  {uf : UnionFind n} {forest : Finset (Sym2 (Fin n))}
  (hf: forest ⊆ G.edgeFinset)
  (hes: es.toFinset ⊆ G.edgeFinset)
  (hsync : ∀ a b, uf.find a = uf.find b → (SimpleGraph.fromEdgeSet forest).Reachable a b) :
  ∀ a b, (kruskalAux G es uf forest).2.find a = (kruskalAux G es uf forest).2.find b →
    (SimpleGraph.fromEdgeSet (kruskalAux G es uf forest).1).Reachable a b := by
  fun_induction kruskalAux
  case case1 => exact hsync
  case case2 =>
    have he : e = s(u, v) := (Quot.out_eq e).symm
    intro a b h_eq
    have h1 : newforest ⊆ G.edgeFinset := by
      dsimp [newforest]
      rw [Finset.insert_subset_iff]
      constructor
      · rw [List.toFinset_cons] at hes
        rw [Finset.insert_subset_iff] at hes
        exact hes.1
      · exact hf
    have h2 : es_1.toFinset ⊆ G.edgeFinset := subsetList hes
    have h3 : ∀ a b, newuf.find a = newuf.find b →
      (SimpleGraph.fromEdgeSet newforest).Reachable a b := by
      dsimp [newuf, newforest]
      intro a b h_eq
      convert sync_preserve_add_edge uf_1 forest_1 e u v he h hsync a b h_eq
      ext x
      simp
    exact ih1 h1 h2 h3 a b h_eq
  case case3 =>
    exact ih1 hf (subsetList hes) hsync

-- Helper lemma: every edge in the edge list has its endpoints reachable in the final forest
lemma kruskalAux_edge_reachable {n: ℕ} {G : WeightedGraph (Fin n)}
  {es : List (Sym2 (Fin n))}
  {uf : UnionFind n} {forest : Finset (Sym2 (Fin n))}
  (hf: forest ⊆ G.edgeFinset)
  (hes: es.toFinset ⊆ G.edgeFinset)
  (hsync : ∀ a b, uf.find a = uf.find b → (SimpleGraph.fromEdgeSet forest).Reachable a b)
  (e : Sym2 (Fin n))
  (he : e ∈ es) :
  let u := e.out.1
  let v := e.out.2
  (SimpleGraph.fromEdgeSet (kruskalAux G es uf forest).1).Reachable u v := by
  fun_induction kruskalAux
  case case1 =>
    simp at he
  case case2 =>
    by_cases h_eq : e = e_1
    · rw [h_eq]
      have he1 : e_1 = s(u, v) := (Quot.out_eq e_1).symm
      have h_uv_adj : (SimpleGraph.fromEdgeSet ({e_1} ∪ forest_1)).Adj u v := by
        rw [he1]
        simp [SimpleGraph.fromEdgeSet_adj]
        intro h_eq_uv
        rw [h_eq_uv] at h
        contradiction
      have h_uv_reach : (SimpleGraph.fromEdgeSet ({e_1} ∪ forest_1)).Reachable u v :=
        SimpleGraph.Adj.reachable h_uv_adj
      have h_sub : ({e_1} ∪ ↑forest_1 : Set (Sym2 (Fin n))) ⊆ ↑(kruskalAux G es_1 newuf newforest).1 := by
        simp
        exact_mod_cast kruskalAux_forest_mono
      exact reachable_mono h_sub h_uv_reach
    · have h_mem : e ∈ es_1 := by
        simp [h_eq] at he
        exact he
      have h1 : newforest ⊆ G.edgeFinset := by
        dsimp [newforest]
        rw [Finset.insert_subset_iff]
        constructor
        · rw [List.toFinset_cons] at hes
          rw [Finset.insert_subset_iff] at hes
          exact hes.1
        · exact hf
      have h_sync : ∀ (a b : Fin n), newuf.find a = newuf.find b → (SimpleGraph.fromEdgeSet ↑newforest).Reachable a b := by
        dsimp [newuf, newforest]
        convert sync_preserve_add_edge uf_1 forest_1 e_1 u v (Quot.out_eq e_1).symm h hsync
        simp
      exact ih1 h1 (subsetList hes) h_sync h_mem
  case case3 =>
    by_cases h_eq : e = e_1
    · rw [h_eq]
      have h_find_eq : uf_1.find u = uf_1.find v := by
        simp at h
        exact h
      have h_final_eq : (kruskalAux G es_1 uf_1 forest_1).2.find u = (kruskalAux G es_1 uf_1 forest_1).2.find v :=
        find_eq_preserved u v h_find_eq
      have h_reach : (SimpleGraph.fromEdgeSet (kruskalAux G es_1 uf_1 forest_1).1).Reachable u v := by
        apply kruskalAux_sync hf (subsetList hes) hsync u v
        exact h_final_eq
      exact h_reach
    · have h_mem : e ∈ es_1 := by
        simp [h_eq] at he
        exact he
      exact ih1 hf (subsetList hes) hsync h_mem

-- Helper lemma: every edge in G has its endpoints reachable in kruskal G
lemma kruskal_edge_reachable {n : ℕ} (G : WeightedGraph (Fin n)) (e : Sym2 (Fin n))
  (he : e ∈ G.edgeFinset) :
  let u := e.out.1
  let v := e.out.2
  (kruskal G).Reachable u v := by
  let es := Finset.sort G.edgeFinset G.byWeight
  have hes : es.toFinset ⊆ G.edgeFinset := by rw [Finset.sort_toFinset]
  have h_mem : e ∈ es := by
    rw [Finset.mem_sort]
    exact he
  have h : (SimpleGraph.fromEdgeSet (kruskalAux G es UnionFind.empty (∅ : Finset (Sym2 (Fin n)))).1).Reachable e.out.1 e.out.2 := by
    apply kruskalAux_edge_reachable
    · exact Finset.empty_subset G.edgeFinset
    · exact hes
    · -- Show sync invariant for initial state
      intro a b h_eq
      have h1 : UnionFind.empty.find a = a := by
        rw [UnionFind.find]
        rw [find_eq]
        simp [UnionFindStructure.make, Forest.make, ArrayN.get, Array.getElem_ofFn]
      have h2 : UnionFind.empty.find b = b := by
        rw [UnionFind.find]
        rw [find_eq]
        simp [UnionFindStructure.make, Forest.make, ArrayN.get, Array.getElem_ofFn]
      rw [h1, h2] at h_eq
      rw [h_eq]
    · exact h_mem
  exact h

-- Helper lemma: adjacent vertices in G are reachable in kruskal G
lemma kruskal_adj_reachable {n : ℕ} (G : WeightedGraph (Fin n)) {u v : Fin n}
  (hAdj : G.Adj u v) : (kruskal G).Reachable u v := by
  have h_edge : s(u, v) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hAdj
  have h_raw := kruskal_edge_reachable G (s(u, v)) h_edge
  generalize h_p : Quot.out s(u, v) = p
  rcases p with ⟨a, b⟩
  have h_a : (Quot.out s(u, v)).1 = a := congr_arg Prod.fst h_p
  have h_b : (Quot.out s(u, v)).2 = b := congr_arg Prod.snd h_p
  rw [h_a, h_b] at h_raw
  have h_eq : s(a, b) = s(u, v) := by
    have h1 : Quot.mk (Sym2.Rel (Fin n)) (Quot.out s(u, v)) = s(u, v) := Quot.out_eq s(u, v)
    rw [h_p] at h1
    exact h1
  rw [Sym2.mk_eq_mk_iff] at h_eq
  cases h_eq with
  | inl h =>
    have h1 : a = u := by injection h
    have h2 : b = v := by injection h
    rw [h1, h2] at h_raw
    exact h_raw
  | inr h =>
    have h1 : a = v := by injection h
    have h2 : b = u := by injection h
    rw [h1, h2] at h_raw
    exact h_raw.symm

-- Helper lemma: Kruskal output is connected (given G is connected)
lemma kruskal_Connected {n : ℕ} (G : WeightedGraph (Fin n)) (hn : n > 0) (hG : G.Connected) :
  (kruskal G).Connected := by
  have h_preconnected : SimpleGraph.Preconnected (kruskal G).toSimpleGraph := by
    intro a b
    have h_reach_G : (G : SimpleGraph (Fin n)).Reachable a b := hG a b
    rcases h_reach_G with ⟨w⟩
    have h : (kruskal G).Reachable a b := by
      induction w with
      | nil => exact SimpleGraph.Reachable.rfl
      | cons hAdj p ih =>
        have h1 : (kruskal G).Reachable _ _ := kruskal_adj_reachable G hAdj
        exact h1.trans ih
    exact h
  haveI : Nonempty (Fin n) := ⟨0, hn⟩
  exact SimpleGraph.Connected.mk h_preconnected

-- Helper lemma: the edge list used by Kruskal is sorted by weight
lemma kruskal_edges_sorted {n : ℕ} (G : WeightedGraph (Fin n)) :
  List.Pairwise G.byWeight (Finset.sort G.edgeFinset G.byWeight) := by
  apply Finset.pairwise_sort

-- Helper lemma: Kruskal weight invariant
lemma kruskalAux_weight_invariant {n : ℕ} {G : WeightedGraph (Fin n)}
  (es : List (Sym2 (Fin n)))
  (uf : UnionFind n) (forest : Finset (Sym2 (Fin n)))
  (hf: forest ⊆ G.edgeFinset)
  (hes: es.toFinset ⊆ G.edgeFinset)
  (hproc : ∀ a b, s(a,b) ∈ G.edgeFinset → s(a,b) ∉ es.toFinset →
    (SimpleGraph.fromEdgeSet forest).Reachable a b)
  (hsorted: List.Pairwise G.byWeight es)
  (hsync : ∀ a b, uf.find a = uf.find b ↔ (SimpleGraph.fromEdgeSet forest).Reachable a b)
  (hinv : ∀ T' : WeightedGraph (Fin n), T'.IsSpanningTree G →
    ∃ T : WeightedGraph (Fin n), T.IsSpanningTree G ∧ forest ⊆ T.edgeFinset ∧ T.weightSum ≤ T'.weightSum) :
  ∀ T' : WeightedGraph (Fin n), T'.IsSpanningTree G →
    ∃ T : WeightedGraph (Fin n), T.IsSpanningTree G ∧
      (kruskalAux G es uf forest).1 ⊆ T.edgeFinset ∧ T.weightSum ≤ T'.weightSum := by
  fun_induction kruskalAux
  · -- Base case: empty edge list
    intro T' hT'
    exact hinv T' hT'
  · -- Case: non-empty edge list, endpoints in different components (add edge)
    intro T' hT'
    have hproc' : ∀ a b, s(a,b) ∈ G.edgeFinset → s(a,b) ∉ es_1.toFinset →
        (SimpleGraph.fromEdgeSet (newforest : Set (Sym2 (Fin n)))).Reachable a b := by
      intro a b ha hb
      by_cases h : s(a, b) = e
      · -- s(a,b) = e = s(u,v), so e is in newforest
        have he : e = s(u, v) := (Quot.out_eq e).symm
        have h_eq : s(a, b) = s(u, v) := by rw [h, he]
        have hmem : s(a, b) ∈ newforest := by
          rw [show s(a, b) = e by rw [h_eq, he]]
          exact Finset.mem_union_left forest_1 (Finset.mem_singleton.mpr rfl)
        have h_adj : (SimpleGraph.fromEdgeSet (newforest : Set (Sym2 (Fin n)))).Adj a b := by
          rw [SimpleGraph.fromEdgeSet_adj]
          constructor
          · exact hmem
          · -- Show a ≠ b
            have h_adj_G : G.Adj a b := by
              rw [←SimpleGraph.mem_edgeSet]
              exact SimpleGraph.mem_edgeFinset.mp ha
            exact h_adj_G.ne
        exact h_adj.reachable
      · -- s(a,b) ≠ e, so s(a,b) ∉ (e :: es_1)
        have : s(a, b) ∉ (e :: es_1).toFinset := by
          rw [List.toFinset_cons]
          intro hmem
          rcases Finset.mem_insert.mp hmem with heq | hmem'
          · exact h heq
          · exact hb hmem'
        have hreach : (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable a b := hproc a b ha this
        have hsub : (forest_1 : Set (Sym2 (Fin n))) ⊆ (newforest : Set (Sym2 (Fin n))) := by
          exact Finset.subset_union_right
        have : (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))) ≤ (SimpleGraph.fromEdgeSet (newforest : Set (Sym2 (Fin n)))) := by
          apply SimpleGraph.fromEdgeSet_mono
          exact hsub
        exact SimpleGraph.Reachable.mono this hreach
    have hsorted' : List.Pairwise G.byWeight es_1 := by
      exact List.Pairwise.of_cons hsorted
    have hes' : es_1.toFinset ⊆ G.edgeFinset := by
      exact subsetList hes
    have hf' : newforest ⊆ G.edgeFinset := by
      dsimp [newforest]
      rw [Finset.insert_subset_iff]
      constructor
      · rw [List.toFinset_cons] at hes
        rw [Finset.insert_subset_iff] at hes
        exact hes.1
      · exact hf
    have hsync' : ∀ a b, newuf.find a = newuf.find b ↔
        (SimpleGraph.fromEdgeSet (newforest : Set (Sym2 (Fin n)))).Reachable a b := by
      intro a b
      have hset_eq : (newforest : Set (Sym2 (Fin n))) = {e} ∪ (forest_1 : Set (Sym2 (Fin n))) := by
        simp [newforest]
      constructor
      · -- Forward: newuf.find a = newuf.find b → Reachable a b
        intro h_eq
        have he : e = s(u, v) := (Quot.out_eq e).symm
        have h_diff : uf_1.find u ≠ uf_1.find v := h
        have hsync_fwd : ∀ a b, uf_1.find a = uf_1.find b → (SimpleGraph.fromEdgeSet forest_1).Reachable a b :=
          fun a b h => (hsync a b).mp h
        have hreach : (SimpleGraph.fromEdgeSet ({e} ∪ forest_1)).Reachable a b :=
          sync_preserve_add_edge uf_1 forest_1 e u v he h_diff hsync_fwd a b h_eq
        rw [hset_eq]
        exact hreach
      · -- Backward: Reachable a b → newuf.find a = newuf.find b
        intro h_reach
        have he : e = s(u, v) := (Quot.out_eq e).symm
        have h_diff : uf_1.find u ≠ uf_1.find v := h
        have hsync_bwd : ∀ x y, (SimpleGraph.fromEdgeSet forest_1).Reachable x y → uf_1.find x = uf_1.find y :=
          fun x y h => (hsync x y).mpr h
        rw [hset_eq] at h_reach
        exact preserve_inv_add_edge uf_1 forest_1 e u v he h_diff hsync_bwd a b h_reach
    have hinv' : ∀ T' : WeightedGraph (Fin n), T'.IsSpanningTree G →
        ∃ T : WeightedGraph (Fin n), T.IsSpanningTree G ∧ newforest ⊆ T.edgeFinset ∧ T.weightSum ≤ T'.weightSum := by
      intro T' hT'
      have h := hinv T' hT'
      rcases h with ⟨M, hM, hsub, hle⟩
      by_cases heM : e ∈ M.edgeFinset
      · -- e ∈ M, so newforest ⊆ M
        use M
        constructor
        · exact hM
        constructor
        · -- Show newforest ⊆ M.edgeFinset
          intro x hx
          simp [newforest] at hx
          rcases hx with hxe | hxf
          · rw [hxe]; exact heM
          · exact hsub hxf
        · exact hle
      · -- e ∉ M, need exchange argument
        have he : e = s(u, v) := (Quot.out_eq e).symm
        have hM_tree : M.IsTree := hM.2
        have hM_sub : M.IsSubgraph G := hM.1
        have hM_conn : M.Connected := hM_tree.1
        have huvM : M.Reachable u v := hM_conn u v
        rcases huvM with ⟨pM⟩
        have hexists_f : ∃ f, f ∈ pM.edges.toFinset ∧ f ∉ forest_1 ∧ f ∈ (e :: es_1).toFinset := by
          by_contra h_all
          push_neg at h_all
          have hreach_uv : (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable u v := by
            have h_ind : ∀ {x y} (p : M.toSimpleGraph.Walk x y),
              (∀ f, f ∈ p.edges.toFinset → f ∉ forest_1 → f ∉ (e :: es_1).toFinset) →
              (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable x y := by
              intro x y p hp
              induction p with
              | nil =>
                exact SimpleGraph.Reachable.rfl
              | @cons a b c h_ab p_bc ih =>
                have h_reach_ab : (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable a b := by
                  by_cases h_forest : s(a, b) ∈ forest_1
                  · -- Edge is in forest_1
                    have h_adj : (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Adj a b := by
                      rw [SimpleGraph.fromEdgeSet_adj]
                      constructor
                      · exact h_forest
                      · exact h_ab.ne
                    exact h_adj.reachable
                  · -- Edge is not in forest_1, so by hp, it's not in (e :: es_1).toFinset
                    have h_not_es : s(a, b) ∉ (e :: es_1).toFinset := by
                      apply hp s(a, b)
                      · simp [SimpleGraph.Walk.edges]
                      · exact h_forest
                    -- Apply hproc
                    have h_G : s(a, b) ∈ G.edgeFinset := by
                      have h_M : s(a, b) ∈ M.edgeSet := by
                        rw [SimpleGraph.mem_edgeSet]
                        exact h_ab
                      have h_M_finset : s(a, b) ∈ M.edgeFinset := by
                        rw [SimpleGraph.mem_edgeFinset]
                        exact h_M
                      have h_sub : M.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hM_sub.1
                      exact h_sub h_M_finset
                    exact hproc a b h_G h_not_es
                have h_reach_bc : (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable b c := by
                  apply ih
                  intro f hf h_forest
                  have hf' : f ∈ (SimpleGraph.Walk.cons h_ab p_bc).edges.toFinset := by
                    simp [SimpleGraph.Walk.edges] at hf ⊢
                    tauto
                  apply hp f hf' h_forest
                exact h_reach_ab.trans h_reach_bc
            apply h_ind pM h_all
          have h_eq : uf_1.find u = uf_1.find v := (hsync u v).mpr hreach_uv
          exact h h_eq
        rcases hexists_f with ⟨f, hf_path, hf_not_forest, hf_es⟩
        have hfM : f ∈ M.edgeFinset := by
          have h1 : f ∈ pM.edges := by
            have h2 : f ∈ pM.edges.toFinset := hf_path
            simp at h2
            exact h2
          have h2 : f ∈ M.edgeSet := SimpleGraph.Walk.edges_subset_edgeSet pM h1
          rw [SimpleGraph.mem_edgeFinset]
          exact h2
        have hfe : f ≠ e := by
          intro h_eq
          rw [h_eq] at hfM
          exact heM hfM
        have hfG : f ∈ G.edgeFinset := by
          have h1 : M.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hM_sub.1
          exact h1 hfM
        have hf_proc : f ∈ (e :: es_1).toFinset := hf_es
        have hweight : G.weight e.out.1 e.out.2 ≤ G.weight f.out.1 f.out.2 := by
          have hf_in_es : f ∈ es_1.toFinset := by
            rw [List.toFinset_cons] at hf_proc
            rcases Finset.mem_insert.mp hf_proc with hfe' | hf_es
            · -- f = e, but we know f ≠ e
              exfalso
              exact hfe (by simpa using hfe')
            · exact hf_es
          have hpairwise : List.Pairwise G.byWeight (e :: es_1) := hsorted
          have hmem : f ∈ e :: es_1 := by
            have h : f ∈ es_1 := by
              have h' : f ∈ es_1.toFinset := hf_in_es
              simp at h'
              exact h'
            simp [h]
          have hf_rel : G.byWeight e f := List.Pairwise.rel_head hpairwise hmem
          simp [WeightedGraph.byWeight] at hf_rel
          cases hf_rel with
          | inl hlt => exact Nat.le_of_lt hlt
          | inr heq => exact Nat.le_of_eq heq.1
        have hM' : ∃ M' : WeightedGraph (Fin n), M'.IsSpanningTree G ∧ newforest ⊆ M'.edgeFinset ∧ M'.weightSum ≤ M.weightSum := by
          have heG : e ∈ G.edgeFinset := by
            have h1 : e ∈ (e :: es_1).toFinset := by
              rw [List.toFinset_cons]
              exact Finset.mem_insert_self e es_1.toFinset
            exact hes h1
          let s' := insert e (M.edgeFinset.erase f)
          have hs'_sub : s' ⊆ G.edgeFinset := by
            have h1 : M.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hM_sub.1
            have h2 : M.edgeFinset.erase f ⊆ M.edgeFinset := Finset.erase_subset f M.edgeFinset
            have h3 : M.edgeFinset.erase f ⊆ G.edgeFinset := Finset.Subset.trans h2 h1
            have h4 : insert e (M.edgeFinset.erase f) ⊆ G.edgeFinset := by
              rw [Finset.insert_subset_iff]
              constructor
              · exact heG
              · exact h3
            exact h4
          let M' := G.FromEdgeSubset s' hs'_sub
          use M'
          constructor
          · -- Show M' is a spanning tree of G
            constructor
            · -- Show M' is a subgraph of G
              exact FromEdgeSubset_IsSubgraph hs'_sub
            · -- Show M' is a tree
              have h1 : M'.toSimpleGraph = SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n))) := by
                simp [M', FromEdgeSubset]
              have h2 : M.toSimpleGraph = SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n))) := by
                rw [←SimpleGraph.fromEdgeSet_edgeSet M.toSimpleGraph]
                rw [SimpleGraph.coe_edgeFinset]
              have h3 : s'.card = M.edgeFinset.card := by
                have h4 : e ∉ M.edgeFinset.erase f := by
                  simp [Finset.mem_erase, heM]
                have h5 : (M.edgeFinset.erase f).card + 1 = M.edgeFinset.card := by
                  rw [Finset.card_erase_add_one hfM]
                have h6 : s'.card = (insert e (M.edgeFinset.erase f)).card := rfl
                rw [h6]
                rw [Finset.card_insert_of_notMem h4]
                omega
              have h4 : M.edgeFinset.card + 1 = Fintype.card (Fin n) := by
                have h5 : M.toSimpleGraph.IsTree := hM_tree
                apply SimpleGraph.IsTree.card_edgeFinset
                exact h5
              have h5 : M'.toSimpleGraph.IsTree := by
                rw [SimpleGraph.isTree_iff_connected_and_card]
                constructor
                · -- Show connected
                  rw [h1]
                  have h6 : (SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n)))).edgeFinset = s' := by
                    have h_no_diag : ∀ x ∈ s', ¬x.IsDiag := by
                      intro x hx
                      simp only [s'] at hx
                      rcases Finset.mem_insert.mp hx with hx | hx
                      · rw [hx, he]
                        have h7 : G.Adj u v := by
                          rw [←SimpleGraph.mem_edgeSet]
                          rw [he] at heG
                          exact SimpleGraph.mem_edgeFinset.mp heG
                        exact h7.ne
                      · have h7 : x ∈ M.edgeFinset := by
                          simp only [Finset.mem_erase] at hx
                          exact hx.2
                        have h8 : x ∈ G.edgeFinset := by
                          have h9 : M.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hM_sub.1
                          exact h9 h7
                        have h9 : ¬x.IsDiag := by
                          have h10 : x ∈ G.edgeFinset := h8
                          rw [SimpleGraph.mem_edgeFinset] at h10
                          intro h_diag
                          exact SimpleGraph.not_mem_edgeSet_of_isDiag G.toSimpleGraph h_diag h10
                        exact h9
                    ext e'
                    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
                    constructor
                    · intro h
                      exact h.1
                    · intro he'
                      exact ⟨he', h_no_diag e' he'⟩
                  have h7 : (SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n)))).edgeFinset.card = M.edgeFinset.card := by
                    rw [h6]
                    exact h3
                  have h8 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).Connected := by
                    rw [←h2]
                    exact hM_conn
                  have h9 : (SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n)))).Connected := by
                    have h10 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).edgeFinset = M.edgeFinset := by
                      have h_no_diag : ∀ x ∈ M.edgeFinset, ¬x.IsDiag := by
                        intro x hx
                        have h11 : x ∈ M.edgeFinset := hx
                        have h12 : x ∈ G.edgeFinset := by
                          have h13 : M.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hM_sub.1
                          exact h13 h11
                        have h13 : ¬x.IsDiag := by
                          have h14 : x ∈ G.edgeFinset := h12
                          rw [SimpleGraph.mem_edgeFinset] at h14
                          intro h_diag
                          exact SimpleGraph.not_mem_edgeSet_of_isDiag G.toSimpleGraph h_diag h14
                        exact h13
                      ext e'
                      simp [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
                      constructor
                      · intro h
                        exact h.1
                      · intro he'
                        exact ⟨he', h_no_diag e' he'⟩
                    have h11 : (SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n)))).edgeFinset.card = (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).edgeFinset.card := by
                      rw [h6, h10]
                      exact h3
                    have h12 : (SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n)))).edgeFinset.card + 1 = Fintype.card (Fin n) := by
                      rw [h7]
                      omega
                    have h13 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).edgeFinset.card + 1 = Fintype.card (Fin n) := by
                      rw [h10]
                      omega
                    have h14 : (SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n)))).IsAcyclic := by
                      have h15 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).IsAcyclic := by
                        rw [←h2]
                        exact hM_tree.2
                      have h16 : (SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n)))).edgeFinset = s' := h6
                      have h17 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).edgeFinset = M.edgeFinset := h10
                      have h18 : s' = insert e (M.edgeFinset.erase f) := rfl
                      rw [h16, h17, h18]
                      have h19 : e ∉ M.edgeFinset.erase f := by
                        simp [Finset.mem_erase, heM]
                      have h20 : (M.edgeFinset.erase f).card + 1 = M.edgeFinset.card := by
                        rw [Finset.card_erase_add_one hfM]
                      have h21 : M.edgeFinset.card + 1 = Fintype.card (Fin n) := by
                        omega
                      have h22 : (insert e (M.edgeFinset.erase f)).card = M.edgeFinset.card := by
                        rw [Finset.card_insert_of_notMem h19]
                        omega
                      have h23 : Fintype.card (Fin n) > 0 := by
                        have h24 : Fintype.card (Fin n) = n := Fintype.card_fin n
                        have h25 : n > 0 := by
                          have h26 : G.Connected := hM_sub.1.to_connected
                          have h27 : Nonempty (Fin n) := h26.nonempty
                          rcases h27 with ⟨x⟩
                          have h28 : x.val < n := x.isLt
                          omega
                        omega
                      have h24 : (insert e (M.edgeFinset.erase f)).card + 1 = Fintype.card (Fin n) := by
                        rw [h22]
                        omega
                      have h25 : (SimpleGraph.fromEdgeSet (insert e (M.edgeFinset.erase f) : Set (Sym2 (Fin n)))).Connected := by
                        have h26 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).Connected := h8
                        have h27 : (SimpleGraph.fromEdgeSet (insert e (M.edgeFinset.erase f) : Set (Sym2 (Fin n)))) =
                          (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).deleteEdges {f} ⊔ SimpleGraph.fromEdgeSet {e} := by
                          ext a b
                          simp [SimpleGraph.fromEdgeSet, SimpleGraph.deleteEdges]
                          constructor
                          · intro h
                            simp at h
                            rcases h with h | h
                            · simp [h, he]
                            · have hne : a ≠ b := h.2
                              have hmem : s(a, b) ∈ M.edgeFinset := h.1
                              have hnf : s(a, b) ≠ f := by
                                intro h_eq
                                rw [h_eq] at hmem
                                exact hf_not_forest hmem
                              simp [hmem, hne, hnf]
                          · intro h
                            simp at h
                            rcases h with h | h
                            · rcases h with ⟨hmem, hne, hnf⟩
                              simp [hmem, hne]
                            · have hne : a ≠ b := h.2
                              have heq : s(a, b) = e := h.1
                              simp [heq, hne]
                        rw [h27]
                        have h28 : ((SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).deleteEdges {f} ⊔ SimpleGraph.fromEdgeSet {e}).Connected := by
                          have h29 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).deleteEdges {f} ⊔ SimpleGraph.fromEdgeSet {e} =
                            (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))) ⊔ SimpleGraph.fromEdgeSet {e} := by
                            ext a b
                            simp [SimpleGraph.deleteEdges]
                            constructor
                            · intro h
                              rcases h with h | h
                              · simp at h
                                rcases h with ⟨hmem, hne, hnf⟩
                                have h1 : s(a, b) ∈ M.edgeFinset := hmem
                                have h2 : s(a, b) ∈ (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).edgeSet := by
                                  simp [SimpleGraph.fromEdgeSet]
                                  exact ⟨h1, hne⟩
                                simp [h2]
                              · simp at h
                                have h1 : s(a, b) = e := h.1
                                have h2 : a ≠ b := h.2
                                simp [h1, h2, he]
                            · intro h
                              simp at h
                              rcases h with h | h
                              · have h1 : s(a, b) ∈ M.edgeFinset := by
                                  simp [SimpleGraph.fromEdgeSet] at h
                                  exact h.1
                                have h2 : s(a, b) ≠ f := by
                                  intro h_eq
                                  rw [h_eq] at h1
                                  exact hf_not_forest h1
                                simp [h1, h.2, h2]
                              · simp at h
                                have h1 : s(a, b) = e := h.1
                                have h2 : a ≠ b := h.2
                                simp [h1, h2]
                          rw [h29]
                          have h30 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n))) ⊔ SimpleGraph.fromEdgeSet {e}).Connected := by
                            have h31 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).Connected := h26
                            have h32 : (SimpleGraph.fromEdgeSet {e}).Connected := by
                              rw [he]
                              have h33 : (SimpleGraph.fromEdgeSet {s(u, v)}).Adj u v := by
                                simp [SimpleGraph.fromEdgeSet]
                              have h34 : (SimpleGraph.fromEdgeSet {s(u, v)}).Reachable u v := h33.reachable
                              have h35 : ∀ a b, (SimpleGraph.fromEdgeSet {s(u, v)}).Reachable a b := by
                                intro a b
                                have h36 : ∀ x, (SimpleGraph.fromEdgeSet {s(u, v)}).Reachable x u ∨ (SimpleGraph.fromEdgeSet {s(u, v)}).Reachable x v := by
                                  intro x
                                  simp [SimpleGraph.fromEdgeSet]
                                  by_cases h37 : x = u
                                  · left
                                    rw [h37]
                                    exact SimpleGraph.Reachable.rfl
                                  · by_cases h38 : x = v
                                    · right
                                      rw [h38]
                                      exact SimpleGraph.Reachable.rfl
                                    · have h39 : ∀ a b, ¬(SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b := by
                                        intro a b
                                        simp [SimpleGraph.fromEdgeSet]
                                        intro h40 h41
                                        have h42 : a = u ∨ a = v := by
                                          simp [Sym2.eq_iff] at h40
                                          cases h40 with
                                          | inl h43 => left; exact h43.1
                                          | inr h43 => right; exact h43.1
                                        have h43 : b = u ∨ b = v := by
                                          simp [Sym2.eq_iff] at h41
                                          cases h41 with
                                          | inl h44 => left; exact h44.2
                                          | inr h44 => right; exact h44.2
                                        rcases h42 with h44 | h44
                                        · rcases h43 with h45 | h45
                                          · rw [h44] at h37; contradiction
                                          · rw [h44, h45]
                                            have h46 : u ≠ v := by
                                              have h47 : G.Adj u v := by
                                                rw [←SimpleGraph.mem_edgeSet]
                                                rw [he] at heG
                                                exact SimpleGraph.mem_edgeFinset.mp heG
                                              exact h47.ne
                                            contradiction
                                        · rcases h43 with h45 | h45
                                          · rw [h44, h45]
                                            have h46 : v ≠ u := by
                                              have h47 : G.Adj u v := by
                                                rw [←SimpleGraph.mem_edgeSet]
                                                rw [he] at heG
                                                exact SimpleGraph.mem_edgeFinset.mp heG
                                              exact h47.ne.symm
                                            contradiction
                                          · rw [h44] at h38; contradiction
                                      have h40 : ∀ x y, (SimpleGraph.fromEdgeSet {s(u, v)}).Reachable x y → x = y := by
                                        intro x y h_reach
                                        induction h_reach with
                                        | refl => rfl
                                        | tail h_reach h_adj ih =>
                                          exfalso
                                          exact h39 _ _ h_adj
                                      have h41 : x = u := by
                                        apply h40 x u
                                        exact h_reach
                                      contradiction
                                have h37 : (SimpleGraph.fromEdgeSet {s(u, v)}).Reachable a b := by
                                  rcases h36 a with h38 | h38
                                  · rcases h36 b with h39 | h39
                                    · exact h38.trans h39.symm
                                    · exact h38.trans h34.trans h39.symm
                                  · rcases h36 b with h39 | h39
                                    · exact h38.trans h34.symm.trans h39.symm
                                    · exact h38.trans h39.symm
                                exact h37
                              have h36 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n))) ⊔ SimpleGraph.fromEdgeSet {e}).Reachable a b := by
                                have h37 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))).Reachable a b := h31 a b
                                have h38 : (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n)))) ≤
                                  (SimpleGraph.fromEdgeSet (M.edgeFinset : Set (Sym2 (Fin n))) ⊔ SimpleGraph.fromEdgeSet {e}) := by
                                  apply SimpleGraph.le_sup_left
                                exact SimpleGraph.Reachable.mono h38 h37
                              exact ⟨h36⟩
                            exact h30
                          exact h28
                        have h26 : (SimpleGraph.fromEdgeSet (insert e (M.edgeFinset.erase f) : Set (Sym2 (Fin n)))).IsTree := by
                          rw [SimpleGraph.isTree_iff_connected_and_card]
                          constructor
                          · exact h25
                          · rw [h6, h10, h18]
                            omega
                        exact h26.2
                      exact h14
                    exact h9
                  exact h9
                · -- Show card condition
                  rw [h1]
                  have h6 : (SimpleGraph.fromEdgeSet (s' : Set (Sym2 (Fin n)))).edgeFinset = s' := by
                    have h_no_diag : ∀ x ∈ s', ¬x.IsDiag := by
                      intro x hx
                      simp [s'] at hx
                      rcases hx with rfl | hx
                      · rw [he]
                        have h7 : G.Adj u v := by
                          rw [←SimpleGraph.mem_edgeSet]
                          rw [he] at heG
                          exact SimpleGraph.mem_edgeFinset.mp heG
                        exact h7.ne
                      · have h7 : x ∈ M.edgeFinset := by
                          simp [Finset.mem_erase] at hx
                          exact hx.2
                        have h8 : x ∈ G.edgeFinset := by
                          have h9 : M.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hM_sub.1
                          exact h9 h7
                        have h9 : ¬x.IsDiag := by
                          have h10 : x ∈ G.edgeFinset := h8
                          rw [SimpleGraph.mem_edgeFinset] at h10
                          intro h_diag
                          exact SimpleGraph.not_mem_edgeSet_of_isDiag G.toSimpleGraph h_diag h10
                        exact h9
                    ext e'
                    simp [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
                    constructor
                    · intro h
                      exact h.1
                    · intro he'
                      exact ⟨he', h_no_diag e' he'⟩
                  rw [h6]
                  omega
              exact h5
          constructor
          · -- Show newforest ⊆ M'.edgeFinset
            intro x hx
            simp [newforest, M', s'] at hx ⊢
            rcases hx with rfl | hx
            · simp
            · have h1 : x ∈ M.edgeFinset := hsub hx
              have h2 : x ≠ f := by
                intro h_eq
                rw [h_eq] at hx
                exact hf_not_forest hx
              simp [h1, h2]
          · -- Show M'.weightSum ≤ M.weightSum
            have h1 : M'.weightSum = ∑ e ∈ s', G.weight e.out.1 e.out.2 := by
              simp [M', weightSum, FromEdgeSubset]
              rfl
            have h2 : M.weightSum = ∑ e ∈ M.edgeFinset, G.weight e.out.1 e.out.2 := by
              have h3 : M.IsSubgraph G := hM_sub
              simp [weightSum]
              apply Finset.sum_congr
              · rfl
              · intro e he
                have h4 : M.Adj e.out.1 e.out.2 := by
                  have h5 : e ∈ M.edgeFinset := he
                  have h6 : e ∈ M.toSimpleGraph.edgeSet := by
                    rw [SimpleGraph.mem_edgeFinset] at h5
                    exact h5
                  rw [SimpleGraph.mem_edgeSet] at h6
                  exact h6
                exact h3.2 e.out.1 e.out.2 h4
            rw [h1, h2]
            have h3 : s' = insert e (M.edgeFinset.erase f) := rfl
            rw [h3]
            have h4 : e ∉ M.edgeFinset.erase f := by
              simp [Finset.mem_erase, heM]
            have h5 : ∑ e ∈ insert e (M.edgeFinset.erase f), G.weight e.out.1 e.out.2 =
              G.weight e.out.1 e.out.2 + ∑ e ∈ M.edgeFinset.erase f, G.weight e.out.1 e.out.2 := by
              rw [Finset.sum_insert h4]
            have h6 : ∑ e ∈ M.edgeFinset, G.weight e.out.1 e.out.2 =
              G.weight f.out.1 f.out.2 + ∑ e ∈ M.edgeFinset.erase f, G.weight e.out.1 e.out.2 := by
              have h7 : ∑ e ∈ M.edgeFinset, G.weight e.out.1 e.out.2 =
                ∑ e ∈ insert f (M.edgeFinset.erase f), G.weight e.out.1 e.out.2 := by
                rw [Finset.insert_erase]
                exact hfM
              rw [h7]
              rw [Finset.sum_insert]
              · simp [Finset.mem_erase]
              · simp [Finset.mem_erase]
            rw [h5, h6]
            exact Nat.add_le_add_right hweight _
        rcases hM' with ⟨M', hM'_tree, hM'_sub, hM'_le⟩
        use M'
        constructor
        · exact hM'_tree
        constructor
        · exact hM'_sub
        · linarith [hM'_le, hle]
    exact ih1 hf' hes' hproc' hsorted' hsync' hinv' T' hT'
  · -- Case: non-empty edge list, endpoints in same component (skip edge)
    intro T' hT'
    have hproc' : ∀ a b, s(a,b) ∈ G.edgeFinset → s(a,b) ∉ es_1.toFinset →
        (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable a b := by
      intro a b ha hb
      by_cases h : s(a, b) = e
      · -- s(a,b) = e = s(u,v), and u,v are in same component
        have he : e = s(u, v) := (Quot.out_eq e).symm
        have h_eq : s(a, b) = s(u, v) := by rw [h, he]
        have h_eq' : uf_1.find u = uf_1.find v := by
          have hne : ¬uf_1.find u ≠ uf_1.find v := by assumption
          simp at hne
          exact hne
        have hreach_uv : (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable u v := (hsync u v).mp h_eq'
        have hreach_ab : (SimpleGraph.fromEdgeSet (forest_1 : Set (Sym2 (Fin n)))).Reachable a b := by
          rw [Sym2.eq_iff] at h_eq
          cases h_eq with
          | inl h_eq1 =>
            have ha : a = u := h_eq1.1
            have hb' : b = v := h_eq1.2
            rw [ha, hb']
            exact hreach_uv
          | inr h_eq2 =>
            have ha : a = v := h_eq2.1
            have hb' : b = u := h_eq2.2
            rw [ha, hb']
            exact hreach_uv.symm
        exact hreach_ab
      · -- s(a,b) ≠ e, so s(a,b) ∉ (e :: es_1)
        have : s(a, b) ∉ (e :: es_1).toFinset := by
          rw [List.toFinset_cons]
          intro hmem
          rcases Finset.mem_insert.mp hmem with heq | hmem'
          · exact h heq
          · exact hb hmem'
        exact hproc a b ha this
    have hsorted' : List.Pairwise G.byWeight es_1 := by
      exact List.Pairwise.of_cons hsorted
    have hes' : es_1.toFinset ⊆ G.edgeFinset := by
      exact subsetList hes
    exact ih1 hf hes' hproc' hsorted' hsync hinv T' hT'

-- CORRECTNESS PROOF : Kruskal Algorithm computes MST
theorem kruskal_computes_MST {n : ℕ} (G: WeightedGraph (Fin n)) (hn: n > 0)
  (hG: G.Connected):
  (kruskal G).IsMST G := by
  constructor
  · -- Show kruskal G is a spanning tree of G
    constructor
    · exact kruskal_IsSubgraph G
    · -- Show kruskal G is a tree: connected and acyclic
      have h1 : (kruskal G).Connected := kruskal_Connected G hn hG
      have h2 : (kruskal G).IsAcyclic := kruskal_IsAcyclic G
      simp [IsTree, SimpleGraph.isTree_iff]
      constructor <;> assumption
  · -- Show kruskal G has minimum weight among all spanning trees
    intro T' hT'
    let es := Finset.sort G.edgeFinset G.byWeight
    have hes : es.toFinset ⊆ G.edgeFinset := by rw [Finset.sort_toFinset]
    have hsorted : List.Pairwise G.byWeight es := kruskal_edges_sorted G
    have hsync : ∀ a b, UnionFind.empty.find a = UnionFind.empty.find b ↔
      (SimpleGraph.fromEdgeSet (↑(∅ : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).Reachable a b := by
      intro a b
      constructor
      · intro h
        have h1 : UnionFind.empty.find a = a := by
          rw [UnionFind.find]
          rw [find_eq]
          simp [UnionFindStructure.make, Forest.make, ArrayN.get, Array.getElem_ofFn]
        have h2 : UnionFind.empty.find b = b := by
          rw [UnionFind.find]
          rw [find_eq]
          simp [UnionFindStructure.make, Forest.make, ArrayN.get, Array.getElem_ofFn]
        rw [h1, h2] at h
        rw [h]
      · intro h
        have h1 : UnionFind.empty.find a = a := by
          rw [UnionFind.find]
          rw [find_eq]
          simp [UnionFindStructure.make, Forest.make, ArrayN.get, Array.getElem_ofFn]
        have h2 : UnionFind.empty.find b = b := by
          rw [UnionFind.find]
          rw [find_eq]
          simp [UnionFindStructure.make, Forest.make, ArrayN.get, Array.getElem_ofFn]
        have h3 : a = b := by
          rcases h with ⟨w⟩
          induction w with
          | nil => rfl
          | cons h_adj p' ih =>
            exfalso
            simp [SimpleGraph.fromEdgeSet] at h_adj
        rw [h3]
    have hproc : ∀ a b, s(a,b) ∈ G.edgeFinset → s(a,b) ∉ es.toFinset →
        (SimpleGraph.fromEdgeSet (∅ : Finset (Sym2 (Fin n)))).Reachable a b := by
      intro a b ha hb
      have h : s(a, b) ∈ es.toFinset := by
        rw [Finset.sort_toFinset]
        exact ha
      contradiction
    have hinv : ∀ T' : WeightedGraph (Fin n), T'.IsSpanningTree G →
      ∃ T : WeightedGraph (Fin n), T.IsSpanningTree G ∧ (∅ : Finset (Sym2 (Fin n))) ⊆ T.edgeFinset ∧ T.weightSum ≤ T'.weightSum := by
      intro T' hT'
      use T'
      constructor
      · exact hT'
      constructor
      · exact Finset.empty_subset T'.edgeFinset
      · exact le_rfl
    have h := kruskalAux_weight_invariant es UnionFind.empty (∅ : Finset (Sym2 (Fin n)))
      (Finset.empty_subset G.edgeFinset) hes hproc hsorted hsync hinv T' hT'
    rcases h with ⟨T, hT, hsub, hle⟩
    have h_eq : (kruskal G).edgeFinset = T.edgeFinset := by
      have h_kruskal_edges : (kruskal G).edgeFinset = (kruskalAux G es UnionFind.empty (∅ : Finset (Sym2 (Fin n)))).1 := by
        have h1 : (kruskal G).edgeFinset ⊆ (kruskalAux G es UnionFind.empty (∅ : Finset (Sym2 (Fin n)))).1 := by
          intro e he
          simp [kruskal, FromEdgeSubset, WeightedGraph.edgeFinset] at he
          exact he.1
        have h2 : (kruskalAux G es UnionFind.empty (∅ : Finset (Sym2 (Fin n)))).1 ⊆ (kruskal G).edgeFinset := by
          intro e he
          simp [kruskal, FromEdgeSubset, WeightedGraph.edgeFinset]
          constructor
          · exact he
          · have hne : e ∈ G.edgeFinset := by
              have hsub' : (kruskalAux G es UnionFind.empty (∅ : Finset (Sym2 (Fin n)))).1 ⊆ G.edgeFinset := by
                apply returns_edge_subset
                exact Finset.empty_subset G.edgeFinset
                exact hes
              exact hsub' he
            have hnd : ¬e.IsDiag := by
              have hne' : e ∈ G.edgeFinset := hne
              rw [SimpleGraph.mem_edgeFinset] at hne'
              intro h_diag
              exact SimpleGraph.not_mem_edgeSet_of_isDiag G.toSimpleGraph h_diag hne'
            exact hnd
        apply Finset.Subset.antisymm h1 h2
      have h1 : (kruskal G).edgeFinset ⊆ T.edgeFinset := by
        rw [h_kruskal_edges]
        exact hsub
      have h2 : (kruskal G).edgeFinset.card = T.edgeFinset.card := by
        have h_kruskal : ((kruskal G).toSimpleGraph).IsTree := by
          simp [SimpleGraph.isTree_iff]
          constructor
          · exact kruskal_Connected G hn hG
          · exact kruskal_IsAcyclic G
        have h_T : (T.toSimpleGraph).IsTree := hT.2
        have h_kruskal_edges : (kruskal G).edgeFinset.card + 1 = Fintype.card (Fin n) := by
          apply SimpleGraph.IsTree.card_edgeFinset
          exact h_kruskal
        have h_T_edges : T.edgeFinset.card + 1 = Fintype.card (Fin n) := by
          apply SimpleGraph.IsTree.card_edgeFinset
          exact h_T
        omega
      apply Finset.eq_of_subset_of_card_le h1
      omega
    have h_weight_eq : (kruskal G).weightSum = T.weightSum := by
      dsimp [weightSum]
      rw [h_eq]
      apply Finset.sum_congr
      · rfl
      · intro e he
        have h1 : (kruskal G).weight e.out.1 e.out.2 = G.weight e.out.1 e.out.2 := by
          have he' : (kruskal G).Adj e.out.1 e.out.2 := by
            have h1 : s(e.out.1, e.out.2) ∈ (kruskal G).edgeFinset := by
              have h_eq_e : s(e.out.1, e.out.2) = e := by
                simp [Sym2.eq_swap]
              rw [h_eq_e]
              rw [show (kruskal G).edgeFinset = T.edgeFinset by rw [h_eq]]
              exact he
            have h2 : s(e.out.1, e.out.2) ∈ (kruskal G).toSimpleGraph.edgeSet := by
              simpa using h1
            rw [SimpleGraph.mem_edgeSet] at h2
            exact h2
          apply (kruskal_IsSubgraph G).2
          exact he'
        have h2 : T.weight e.out.1 e.out.2 = G.weight e.out.1 e.out.2 := by
          have he' : T.Adj e.out.1 e.out.2 := by
            have h1 : s(e.out.1, e.out.2) ∈ T.edgeFinset := by
              have h_eq_e : s(e.out.1, e.out.2) = e := by
                simp [Sym2.eq_swap]
              rw [h_eq_e]
              exact he
            have h2 : s(e.out.1, e.out.2) ∈ T.toSimpleGraph.edgeSet := by
              simpa using h1
            rw [SimpleGraph.mem_edgeSet] at h2
            exact h2
          apply hT.1.2
          exact he'
        rw [h1, h2]
    rw [h_weight_eq]
    exact hle
