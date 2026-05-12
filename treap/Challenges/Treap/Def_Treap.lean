/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.BigOperators
import Cslib.Algorithms.Lean.TimeM

set_option linter.style.longLine false
namespace Cslib.Algorithms.Lean.TimeM
namespace TreapLogic
open Tree


/-
  Base Treap definitions and properties

  We use implicit type variables for functions. structures and abbrevs are defined explicitely.
  LinearOrder is required for both Key and Prio types to enable comparisons
-/
variable {Key : Type} [LinearOrder Key]
variable {Prio : Type} [LinearOrder Prio]

-- A single Treap Node Type
structure KeyPrioPair (Key : Type) (Prio : Type) [LinearOrder Key] [LinearOrder Prio] where
  key : Key
  prio : Prio

-- Abbreviation for a TreapNode, which is a Tree of KeyPrioPairs
abbrev TreapNode (Key : Type) (Prio : Type)
[LinearOrder Key] [LinearOrder Prio] := Tree (KeyPrioPair Key Prio)

-- Getter for root node key-priority pair
def TreapNode.root : TreapNode Key Prio → Option (KeyPrioPair Key Prio)
  | Tree.nil => none
  | Tree.node (kp : KeyPrioPair Key Prio) _ _ => some kp

-- Getter for root node key
def TreapNode.key : TreapNode Key Prio → Option Key
  | Tree.nil => none
  | Tree.node (kp : KeyPrioPair Key Prio) _ _ => some kp.key

-- Getter for root node priority
def TreapNode.prio : TreapNode Key Prio → Option Prio
  | Tree.nil => none
  | Tree.node (kp : KeyPrioPair Key Prio) _ _ => some kp.prio

-- Getter for all nodes
def TreapNode.all_nodes : TreapNode Key Prio → Set (KeyPrioPair Key Prio)
  | Tree.nil => ∅
  | Tree.node (kp : KeyPrioPair Key Prio) l r => (all_nodes l) ∪ {kp} ∪ (all_nodes r)

-- Getter for all keys in the treap
def TreapNode.all_keys : TreapNode Key Prio → Set Key
  | Tree.nil => ∅
  | Tree.node (kp : KeyPrioPair Key Prio) l r => (all_keys l) ∪ {kp.key} ∪ (all_keys r)

-- Getter for all priorities in the treap
def TreapNode.all_prios : TreapNode Key Prio → Set Prio
  | Tree.nil => ∅
  | Tree.node (kp : KeyPrioPair Key Prio) l r => (all_prios l) ∪ {kp.prio} ∪ (all_prios r)

-- Useful methods, self explanatory
def TreapNode.all_keys_left : TreapNode Key Prio → Set Key
  | Tree.nil => ∅
  | Tree.node _ l _ => all_keys l

def TreapNode.all_keys_right : TreapNode Key Prio → Set Key
  | Tree.nil => ∅
  | Tree.node _ _ r => all_keys r

def TreapNode.all_prios_left : TreapNode Key Prio → Set Prio
  | Tree.nil => ∅
  | Tree.node _ l _ => all_prios l

def TreapNode.all_prios_right : TreapNode Key Prio → Set Prio
  | Tree.nil => ∅
  | Tree.node _ _ r => all_prios r

/-
  Treap properties
-/

-- BST property
inductive IsBST : (TreapNode Key Prio) → Prop
  | nil : IsBST Tree.nil
  | node (tn : KeyPrioPair Key Prio) (l r : TreapNode Key Prio) :
    -- Require all keys in left subtree < current node key
    (∀ k, k ∈ l.all_keys → k < tn.key) →
    -- Require all keys in right subtree ≥ current node key
    (∀ k, k ∈ r.all_keys → tn.key ≤ k) →
    -- Recursively require left and right subtrees to also satisfy BST property
    IsBST l → IsBST r →
    -- Conclude that the current node satisfies the BST property
    IsBST (Tree.node tn l r)

-- Heap property
inductive IsHeap : (TreapNode Key Prio) → Prop
  | nil : IsHeap Tree.nil
  | node (tn : KeyPrioPair Key Prio) (l r : TreapNode Key Prio) :
    -- Require priority of current node to be >=
    -- priorities of all left and right subtrees (stricter but easier to prove,
    -- equivalent to the local max version)
    (∀ p, p ∈ l.all_prios → p ≤ tn.prio) →
    (∀ p, p ∈ r.all_prios → p ≤ tn.prio) →
    -- Recursively require left and right subtrees to also satisfy heap property
    IsHeap l → IsHeap r →
    -- Conclude that the current node satisfies the heap property
    IsHeap (Tree.node tn l r)

-- Treap property: both BST and Heap properties
def IsTreap (tn : TreapNode Key Prio) : Prop := IsHeap tn ∧ IsBST tn

-- Treap structure contains treap properties + the data
structure Treap (Key : Type) (Prio : Type) [LinearOrder Key] [LinearOrder Prio] where
  root : TreapNode Key Prio
  is_treap : IsTreap root

/-
  Base methods

  We define all methods on TreapNodes, then migrate them to Treaps, proving their correctness there
-/

-- If the treap node is empty
def TreapNode.isEmpty (tn : TreapNode Key Prio) : Bool :=
  match tn with
  | Tree.nil => true
  | _ => false

-- Builder for singleton treap nodes
def TreapNode.singleton (kp : KeyPrioPair Key Prio) : TreapNode Key Prio :=
  Tree.node kp Tree.nil Tree.nil

-- Get the leftmost key in the treap
def TreapNode.leftmost (tn : TreapNode Key Prio) : Option (KeyPrioPair Key Prio) :=
  match tn with
  | Tree.nil => none
  | Tree.node kp l _ =>
    match l with
    | Tree.nil => some kp
    | Tree.node _ _ _ => TreapNode.leftmost l

-- Split the treap in two disjoint treaps, at key value k
-- Cartesian product to return pair of values
def TreapNode.split (tn : TreapNode Key Prio) (k : Key) : TreapNode Key Prio × TreapNode Key Prio :=
  match tn with
  | Tree.nil => (Tree.nil, Tree.nil)
  | Tree.node kp l r =>
    if kp.key < k then
      -- Root goes left, split right
      let (split_l, new_r) := TreapNode.split r k
      -- Return a (l, split_l) treap and a (new_r) treap
      let new_l := Tree.node kp l split_l
      (new_l, new_r)
    else
      -- Root goes right, split left
      let (new_l, split_r) := TreapNode.split l k
      -- Return (new_l) treap and (split_r, r) treap
      let new_r := Tree.node kp split_r r
      (new_l, new_r)

-- Alternative split, to split with l ≤ k < r
-- This is used for inserts/deletes
def TreapNode.splitUpper (tn : TreapNode Key Prio) (k : Key) :
    TreapNode Key Prio × TreapNode Key Prio :=
  match tn with
  | Tree.nil => (Tree.nil, Tree.nil)
  | Tree.node kp l r =>
    if kp.key ≤ k then
      -- Root goes left, splitUpper right
      let (split_l, new_r) := TreapNode.splitUpper r k
      -- Return a (l, split_l) treap and a (new_r) treap
      let new_l := Tree.node kp l split_l
      (new_l, new_r)
    else
      -- Root goes right, splitUpper left
      let (new_l, split_r) := TreapNode.splitUpper l k
      -- Return (new_l) treap and (split_r, r) treap
      let new_r := Tree.node kp split_r r
      (new_l, new_r)

-- Merge two sorted, disjoint treaps
def TreapNode.merge (l r : TreapNode Key Prio) : TreapNode Key Prio :=
  match l, r with
  | Tree.nil, Tree.nil => Tree.nil
  | Tree.nil, Tree.node _ _ _ => r
  | Tree.node _ _ _, Tree.nil => l
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    -- We have to choose the root, use priorities
    if kp_1.prio ≥ kp_2.prio then
      -- Left goes as root
      let new_l := l_1
      let new_r := TreapNode.merge r_1 (Tree.node kp_2 l_2 r_2)
      Tree.node kp_1 new_l new_r
    else
      -- Right as root
      let new_l := TreapNode.merge (Tree.node kp_1 l_1 r_1) l_2
      let new_r := r_2
      Tree.node kp_2 new_l new_r

/-
  Singleton correctness
-/

-- Singleton is a BST
theorem singleton_isBST (kp : KeyPrioPair Key Prio) :
    IsBST (TreapNode.singleton kp) := by
  apply IsBST.node <;> simp_all [TreapNode.all_keys, IsBST.nil]

-- Singleton is a Heap
theorem singleton_isHeap (kp : KeyPrioPair Key Prio) :
    IsHeap (TreapNode.singleton kp) := by
  apply IsHeap.node <;> simp_all [TreapNode.all_prios, IsHeap.nil]

/-
  Treap operations (joint correctness and operation)
-/


def Treap.empty : Treap Key Prio :=
  { root := Tree.nil,
    is_treap := by
      simp [IsTreap, IsBST.nil, IsHeap.nil] }

def Treap.singleton (kp : KeyPrioPair Key Prio) : Treap Key Prio :=
  let root := TreapNode.singleton kp
  have singleton_bst_proof : IsBST root := singleton_isBST kp
  have singleton_heap_proof : IsHeap root := singleton_isHeap kp
  have treap_proof : IsTreap root := by
    simp_all [IsTreap]
  { root := root, is_treap := treap_proof }

-- Leftmost doesn't need correctness proofs here as it doesn't produce new treaps
def Treap.leftmost (t : Treap Key Prio) : Option (KeyPrioPair Key Prio) :=
  -- Delegate the call
  TreapNode.leftmost t.root

def get_key (okp : Option (KeyPrioPair Key Prio)) :=
  match okp with
  | none => none
  | some kp => some kp.key

/-
  Split complexity
-/
def splitT (tn : TreapNode Key Prio) (k : Key) : TimeM (TreapNode Key Prio × TreapNode Key Prio) := do
  match tn with
  | Tree.nil => return (Tree.nil, Tree.nil)
  | Tree.node kp l r =>
    if kp.key < k then
      -- Root goes left, split right
      let (split_l, new_r) ← splitT r k
      -- Return a (l, split_l) treap and a (new_r) treap
      let new_l := Tree.node kp l split_l
      ✓ return (new_l, new_r)
    else
      -- Root goes right, split left
      let (new_l, split_r) ← splitT l k
      -- Return (new_l) treap and (split_r, r) treap
      let new_r := Tree.node kp split_r r
      ✓ return (new_l, new_r)

/-
  SplitUpper complexity
-/
def splitUpperT (tn : TreapNode Key Prio) (k : Key) : TimeM (TreapNode Key Prio × TreapNode Key Prio) := do
  match tn with
  | Tree.nil => return (Tree.nil, Tree.nil)
  | Tree.node kp l r =>
    if kp.key ≤ k then
      -- Root goes left, splitUpper right
      let (splitUpper_l, new_r) ← splitUpperT r k
      -- Return a (l, splitUpper_l) treap and a (new_r) treap
      let new_l := Tree.node kp l splitUpper_l
      ✓ return (new_l, new_r)
    else
      -- Root goes right, splitUpper left
      let (new_l, splitUpper_r) ← splitUpperT l k
      -- Return (new_l) treap and (splitUpper_r, r) treap
      let new_r := Tree.node kp splitUpper_r r
      ✓ return (new_l, new_r)

/-
  Merge complexity
-/
def mergeT (l r : TreapNode Key Prio) : TimeM (TreapNode Key Prio) := do
  match l, r with
  | Tree.nil, Tree.nil => return Tree.nil
  | Tree.nil, Tree.node _ _ _ => ✓ return r
  | Tree.node _ _ _, Tree.nil => ✓ return l
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    -- We have to choose the root, use priorities
    if kp_1.prio ≥ kp_2.prio then
      -- Left goes as root
      let new_l := l_1
      let new_r ← mergeT r_1 (Tree.node kp_2 l_2 r_2)
      ✓ return (Tree.node kp_1 new_l new_r)
    else
      -- Right as root
      let new_l ← mergeT (Tree.node kp_1 l_1 r_1) l_2
      let new_r := r_2
      ✓ return (Tree.node kp_2 new_l new_r)

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
