/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isabel Haas, Pratyai Mazumder, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Challenges.Minimum_Spanning_Tree.Def_ForestN

set_option autoImplicit false
set_option tactic.hygienic false

/--
The UnionFind structure is a wrapper around the `Forest` structure, providing
the standard Disjoint Set Union (DSU) operations. It maintains a collection
of disjoint sets, where each set is represented by a tree in the forest.
-/
def UnionFindStructure (n : ℕ) := Forest n

/--
Creates a new UnionFind structure of size `n`.
Initially, every element is in its own set (i.e., every node is a root).
-/
def UnionFindStructure.make {n : ℕ} : UnionFindStructure n := Forest.make

-- =============================================================================
-- Core Definitions: Find & Union (Standard & Compressed)
-- =============================================================================

-- -----------------------------------------------------------------------------
-- 1. Standard Find (No Compression)
-- -----------------------------------------------------------------------------

/--
Finds the representative (root) of the set containing element `i`.
This implementation uses simple path following without path compression.
Terminates because the forest is acyclic (well-founded).
-/
def UnionFindStructure.find {n : ℕ} (s : UnionFindStructure n) (i : Fin n) : Fin n :=
  let step (x : Fin n)
      (loop : ∀ p, ParentRel (fun k => s.parent.get k) p x → Fin n)
      : Fin n :=
    match h : s.parent.get x with
    | none => x
    | some p => loop p (by simp [ParentRel, h])
  s.acyclic.fix step i

/--
Equational lemma for `find`, hiding the `WellFounded.fix` implementation detail.
-/
lemma find_eq {n : ℕ} (s : UnionFindStructure n) (x : Fin n) :
    s.find x = match s.parent.get x with
               | none => x
               | some p => s.find p := by
  rw [UnionFindStructure.find, WellFounded.fix_eq]
  split <;> simp_all
  rfl

/--
`find` always returns a root of the forest.
-/
lemma find_returns_root {n : ℕ} (s : UnionFindStructure n) (x : Fin n) : s.isRoot (s.find x) := by
  apply Forest.induction s (P := fun k => s.isRoot (s.find k))
  . intro x h_root
    rw [find_eq, h_root]
    exact h_root
  . intro x p h_parent ih
    rw [find_eq, h_parent]
    exact ih


-- -----------------------------------------------------------------------------
-- 2. Standard Union (Union by Rank)
-- -----------------------------------------------------------------------------

/--
Helper function to union two *known* roots using union-by-rank.
Attaches the shorter tree to the taller one to keep the tree height logarithmic.
If ranks are equal, one rank is incremented.
-/
def UnionFindStructure.union_roots {n : ℕ} (s : UnionFindStructure n) (cx cy : Fin n)
    (h_cx : s.isRoot cx)
    (h_cy : s.isRoot cy)
    (h_cxcy : cx ≠ cy) : UnionFindStructure n :=
  let rx := s.rank.get cx
  let ry := s.rank.get cy
  if rx < ry then s.graft cx cy h_cy h_cxcy
  else if rx > ry then s.graft cy cx h_cx h_cxcy.symm
  else
    -- Ranks are equal. Graft cy -> cx and increment cx's rank.
    let s' := s.graft cy cx h_cx h_cxcy.symm
    { s' with rank := s'.rank.set cx (rx + 1) }

/--
Merges the sets containing elements `x` and `y`.
Uses `find` to locate the roots and `union_roots` to merge them if they are different.
-/
def UnionFindStructure.union {n : ℕ} (s : UnionFindStructure n) (x y : Fin n) : UnionFindStructure n :=
  let root_x := s.find x
  let root_y := s.find y
  if h : root_x = root_y then s
  else s.union_roots root_x root_y (find_returns_root s x) (find_returns_root s y) h
