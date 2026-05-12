/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai· All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isabel Haas, Pratyai Mazumder, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Dart

set_option autoImplicit false
set_option tactic.hygienic false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

-- small lemmas used multiple times
lemma subsetList {α : Type} [DecidableEq α] {x : α} {xs : List α} {A : Finset α}
  (h: (x::xs).toFinset ⊆ A):
  xs.toFinset ⊆ A := by
  rw [List.toFinset_cons] at h
  rw [Finset.insert_subset_iff] at h
  exact h.2

lemma subsetSet {α : Type} [DecidableEq α] {x : α} {xs : Finset α} {ys : Finset α}
  (h: insert x xs ⊆ ys):
  xs ⊆ ys := by
  rw [Finset.insert_subset_iff] at h
  exact h.2

lemma memconsrw {α : Type} [DecidableEq α] {x y : α} {xs : List α}: x ∈ (y :: xs).toFinset
  ↔ (x = y ∨ x ∈ xs.toFinset)
:= by
  constructor
  · intro h
    aesop
  · intro h
    aesop

lemma subset_comb {α : Type} [DecidableEq α] {x : α} {es : List α} {xs : Finset α} {A : Finset α}
  (h1 : (x::es).toFinset ⊆ A) (h2 : xs ⊆ A):
  insert x xs ⊆ A := by
  apply Finset.insert_subset
  · rw [List.toFinset_cons] at h1
    rw [Finset.insert_subset_iff] at h1
    exact h1.1
  · exact h2

-- == WeightedGraph definition built on Mathlib Simplegraph ==

@[ext]
structure WeightedGraph (V : Type) extends SimpleGraph V where
  weight : V → V → ℕ
  weight_symm : ∀ {u v}, weight u v = weight v u
  weight_zero_iff_not_adj : ∀ {u v}, weight u v = 0 ↔ ¬ toSimpleGraph.Adj u v

instance {V} : Coe (WeightedGraph V) (SimpleGraph V) :=
  ⟨WeightedGraph.toSimpleGraph⟩
instance {V : Type} [DecidableEq V] (G : WeightedGraph V) :
    DecidableRel G.Adj :=
by
  intro u v
  have h := G.weight_zero_iff_not_adj (u := u) (v := v)
  have : Decidable (¬ G.weight u v = 0) := by
    exact instDecidableNot
  simpa [G.weight_zero_iff_not_adj] using this

noncomputable instance {V : Type} [DecidableEq V] (G : SimpleGraph V) :
    DecidableRel G.Adj :=
by
  intro u v
  exact Classical.propDecidable (G.Adj u v)

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G H : WeightedGraph V}
namespace WeightedGraph

universe u


-- == WeightedGraph methods and theorems ==
-- inductive Walk {G: WeightedGraph V} : V → V → Type u
--   | nil {u : V} : Walk u u
--   | cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w
--   deriving DecidableEq
abbrev Walk :=
  SimpleGraph.Walk (G : SimpleGraph V)

namespace Walk

abbrev IsCycle {u : V} (p : G.Walk u u): Prop :=
  SimpleGraph.Walk.IsCycle p
end Walk

abbrev IsAcyclic: Prop :=
  SimpleGraph.IsAcyclic (G : SimpleGraph V)
abbrev Connected: Prop :=
  SimpleGraph.Connected (G : SimpleGraph V)
abbrev IsTree: Prop :=
  SimpleGraph.IsTree (G : SimpleGraph V)
abbrev connected_iff :=
  SimpleGraph.connected_iff (G : SimpleGraph V)

-- Empty weighted graph

def emptyGraph : WeightedGraph V where
  toSimpleGraph := SimpleGraph.emptyGraph V
  weight := fun _ _ ↦ 0
  weight_symm := by intros; rfl
  weight_zero_iff_not_adj := by
    intro u v
    exact (iff_true_right fun a ↦ a).mpr rfl
@[simps]
instance : Inhabited (WeightedGraph V) := ⟨emptyGraph⟩


-- Edge Set
abbrev edgeFinset: Finset (Sym2 V) :=
  SimpleGraph.edgeFinset (G : SimpleGraph V)

-- Subgraph definition
def IsSubgraph (H G : WeightedGraph V) : Prop :=
  SimpleGraph.IsSubgraph (H : SimpleGraph V) (G : SimpleGraph V) ∧
  -- additionally, weights have to be the same
  (∀ u v, H.Adj u v → H.weight u v = G.weight u v)



--  SimpleGraph.FromEdgeSet returns a subgraph of sG
lemma SimpleGraph.from_edge_subset_is_subgraph (sG : WeightedGraph V) (s: Set (Sym2 V))
  (hset: s ⊆ sG.edgeFinset):
   SimpleGraph.fromEdgeSet s ≤ sG.toSimpleGraph :=
  by
  apply SimpleGraph.fromEdgeSet_mono at hset
  rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] at hset
  exact hset


-- Creates graph from edgeSubset, sG provides weight function
def FromEdgeSubset (sG : WeightedGraph V) (s: Finset (Sym2 V))
  (hset: s ⊆ sG.edgeFinset): WeightedGraph V :=
  let uG := SimpleGraph.fromEdgeSet s
  { toSimpleGraph := uG
    weight :=  fun x y => if h : uG.Adj x y then sG.weight x y else 0
    weight_symm := by
      intro u v
      have h := weight_symm sG (u := u) (v := v)
      split_ifs
      · exact h
      · expose_names
        apply SimpleGraph.adj_symm at h_1
        contradiction
      · expose_names
        apply SimpleGraph.adj_symm at h_2
        contradiction
      · rfl
    weight_zero_iff_not_adj := by
      intro u v
      have h := weight_zero_iff_not_adj sG (u := u) (v := v)
      split_ifs
      · expose_names
        apply SimpleGraph.from_edge_subset_is_subgraph at hset
        rw [SimpleGraph.le_iff_adj] at hset
        have h2 := hset u v
        aesop
      · aesop
    }



-- == Definition of Minimum Spanning Tree ==
def IsSpanningTree (H G : WeightedGraph V) : Prop :=
  H.IsSubgraph G ∧ H.IsTree
-- weight sum of graph
noncomputable def weightSum  (G : WeightedGraph V) : ℕ :=
  ∑ e ∈ G.edgeFinset, G.weight e.out.1 e.out.2
def IsMST (T G: WeightedGraph V) : Prop :=
  T.IsSpanningTree G ∧
  (∀ T' : WeightedGraph V, T'.IsSpanningTree G → T.weightSum ≤ T'.weightSum)


end  WeightedGraph


-- == Definition of a linear order on edge list ==

noncomputable def WeightedGraph.EdgeList (G : WeightedGraph V) : List (Sym2 V) :=
   G.edgeFinset.toList

def Sym2order
  (a b : Sym2 V)  :=
  let (x, y) := a.out
  let (s, t) := b.out
  let (mina, maxa) := (if x ≤ y then (x,y) else (y,x))
  let (minb, maxb) := (if s ≤ t then (s,t) else (t,s))
  mina < minb ∨ (mina = minb ∧ maxa <= maxb)


instance : IsTrans (Sym2 V) (Sym2order) := by
  refine { trans := ?_ }
  unfold Sym2order
  grind


lemma Sym2Components {a b : Sym2 V}
  (h1 : (Quot.out a).1 = (Quot.out b).1)
  (h2 : (Quot.out a).2 = (Quot.out b).2) : a = b :=
  by
  have hp : ∃ p : V × V, p = a.out := exists_apply_eq_apply (fun a ↦ a) (Quot.out a)
  have hq : ∃ q : V × V, q = b.out := exists_apply_eq_apply (fun a ↦ a) (Quot.out b)
  have ⟨p,hp⟩ := hp
  have ⟨q,hq⟩ := hq
  have hp2 : Sym2.mk p = a := by
    rw [hp]
    exact Quot.out_eq a
  have hq2 : Sym2.mk q = b := by
    rw [hq]
    exact Quot.out_eq b
  grind

variable {P: V × V}

lemma Sym2Components_symm {a b : Sym2 V}
  (h1 : (Quot.out a).1 = (Quot.out b).2)
  (h2 : (Quot.out a).2 = (Quot.out b).1) : a = b :=
  by
  have hp : ∃ p : V × V, p = a.out := exists_apply_eq_apply (fun a ↦ a) (Quot.out a)
  have hq : ∃ q : V × V, q = b.out := exists_apply_eq_apply (fun a ↦ a) (Quot.out b)
  have ⟨p,hp⟩ := hp
  have ⟨q,hq⟩ := hq
  have hp2 : Sym2.mk p = a := by
    rw [hp]
    exact Quot.out_eq a
  have hq2 : Sym2.mk q = b := by
    rw [hq]
    exact Quot.out_eq b
  rw [← hp2, ← hq2]
  rw [Sym2.mk_eq_mk_iff]
  right
  grind

instance : IsAntisymm (Sym2 V) (Sym2order) := by
  refine { antisymm := ?_ }
  unfold Sym2order
  simp
  intro a b ha hb
  split_ifs at ha
  <;> split_ifs at hb
  <;> obtain ha | ha := ha
  <;> obtain hb | hb := hb
  <;> expose_names
  <;> (try (
    grw [hb] at ha
    apply lt_irrefl at ha
    contradiction
  ))
  <;> (try (
    grw [hb.1] at ha
    apply lt_irrefl at ha
    contradiction
  ))
  <;> (try (
    rw [ha.1] at hb
    apply lt_irrefl at hb
    contradiction
  ))
  · have h1 := ha.1
    have h2 := le_antisymm ha.2 hb.2
    exact Sym2Components h1 h2
  · have h1 := ha.1
    have h2 := le_antisymm ha.2 hb.2
    exact Sym2Components_symm h1 h2
  · simp at ha hb
    have h1 := ha.1
    have h2 := le_antisymm ha.2 hb.2
    exact Sym2Components_symm h2 h1
  · simp at ha hb
    have h1 := ha.1
    have h2 := le_antisymm ha.2 hb.2
    exact Sym2Components h2 h1

lemma helper ( a b c d : V ):
  (a < b ∨ (a = b ∧ c ≤ d)) ∨ (b < a ∨ (b = a ∧ d ≤ c))
     := by
    have h1 := lt_trichotomy a  b
    obtain h1 | (h1 | h1) := h1
    · left; left; exact h1
    · have h2 := lt_trichotomy c d
      obtain h2 | (h2 | h2) := h2
      · left; right; constructor; exact h1; exact le_of_lt h2
      · left; right; constructor; exact h1; exact le_of_eq h2
      · right; right; constructor; exact h1.symm; exact le_of_lt h2
    · right; left; exact h1

instance : IsTotal (Sym2 V) Sym2order := by
  refine { total := ?_ }
  unfold Sym2order
  simp
  intro a b
  split_ifs <;> expose_names
  · exact helper (Quot.out a).1 (Quot.out b).1 (Quot.out a).2 (Quot.out b).2
  · simp
    exact helper (Quot.out a).1 (Quot.out b).2 (Quot.out a).2 (Quot.out b).1
  · simp
    exact helper (Quot.out a).2 (Quot.out b).1 (Quot.out a).1 (Quot.out b).2
  · simp
    exact helper (Quot.out a).2 (Quot.out b).2 (Quot.out a).1 (Quot.out b).1


def WeightedGraph.byWeight (G : WeightedGraph V) (a b : Sym2 V) : Prop :=
  (G.weight a.out.1 a.out.2) < (G.weight b.out.1 b.out.2) ∨
  ((G.weight a.out.1 a.out.2) = (G.weight b.out.1 b.out.2) ∧ Sym2order a b)


noncomputable instance (G : WeightedGraph V) : DecidableRel (G.byWeight)
  := Classical.decRel G.byWeight
instance (G : WeightedGraph V) : IsTrans (Sym2 V) (G.byWeight) := by
  refine { trans := ?_ }
  unfold WeightedGraph.byWeight
  intros a b c h1 h2
  cases h1
  · left; omega
  · cases h2
    · left
      omega
    · right
      constructor
      · rw [h.1]
        exact h_1.1
      · trans b
        exact h.2
        exact h_1.2

instance (G : WeightedGraph V) : IsAntisymm (Sym2 V) (G.byWeight) := by
  refine { antisymm := ?_ }
  unfold WeightedGraph.byWeight
  intro a b h1 h2
  cases h1
  · omega
  · cases h2
    · omega
    · have h1 := h.2
      have h2 := h_1.2
      exact (@antisymm (Sym2 V) Sym2order) h1 h2


instance (G : WeightedGraph V) : IsTotal (Sym2 V) (G.byWeight) := by
    refine { total := ?_ }
    unfold WeightedGraph.byWeight
    intros a b
    by_cases h1: G.weight (Quot.out a).1 (Quot.out a).2 < G.weight (Quot.out b).1 (Quot.out b).2
    · left; left; exact h1
    · simp at h1
      rw [le_iff_eq_or_lt] at h1
      cases h1
      · have h : Sym2order a b ∨ Sym2order b a := by
          apply total_of
        cases h
        · left; right; exact ⟨h.symm, h_1⟩
        · right; right; exact ⟨h, h_1⟩
      · right
        left
        exact h
