/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isabel Haas, Pratyai Mazumder, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Challenges.Minimum_Spanning_Tree.Def_ArrayN

set_option autoImplicit false
set_option tactic.hygienic false

/--
`ParentRel get_parent p c` defines a relation where `p` is the parent of `c`.
This is used to define well-foundedness (acyclicity) of the forest.
-/
def ParentRel {α : Type} (get_parent : α → Option α) (p c : α) : Prop :=
  get_parent c = some p

/--
The core `Forest` data structure for a Union-Find implementation.
- `parent`: Maps each node to its parent, or `none` if it is a root.
- `rank`: An upper bound on the height of the tree rooted at each node.
- `acyclic`: A proof that the parent relation is well-founded (no cycles).
-/
@[ext]
structure Forest (n : ℕ) where
  parent : ArrayN (Option (Fin n)) n
  rank : ArrayN ℕ n
  acyclic : WellFounded (ParentRel (fun i => parent.get i))

/-- `f.isRoot i` is true if node `i` has no parent in forest `f`. -/
def Forest.isRoot {n : ℕ} (f : Forest n) (i : Fin n) : Prop :=
  f.parent.get i = none

/-- Create a new forest of size `n` where every node is its own root. -/
def Forest.make {n : ℕ} : Forest n := {
  parent := ⟨Array.ofFn (fun i => none), by exact Array.size_ofFn⟩,
  rank := ⟨Array.replicate n 0, by exact Array.size_replicate⟩,
  acyclic := by
    apply WellFounded.intro
    intro i
    apply Acc.intro
    intro p h
    simp [ParentRel, ArrayN.get] at h
}

/--
Generalized induction principle for parent-based well-founded relations.
Allows proving a property `P` for all nodes by showing:
1. Base case: `P` holds for all roots (nodes with no parent).
2. Inductive step: If `P` holds for a parent `p`, it holds for its child `x`.
-/
theorem Forest.induction_on_parent {α : Type} {get_parent : α → Option α}
    (wf : WellFounded (ParentRel get_parent))
    {P : α → Prop}
    (base : ∀ x, get_parent x = none → P x)
    (step : ∀ x p, get_parent x = some p → P p → P x)
    (x : α) : P x := by
  induction x using wf.induction with
  | h x ih =>
    match h : get_parent x with
    | none => exact base x h
    | some p => exact step x p h (ih p h)

/--
Custom induction principle for the Forest structure.
Allows proving a property `P` for all nodes by showing:
1. Base case: `P` holds for all roots.
2. Inductive step: If `P` holds for a parent `p`, it holds for its child `x`.
-/
theorem Forest.induction {n : ℕ} (s : Forest n)
    {P : Fin n → Prop}
    (base : ∀ x, s.isRoot x → P x)
    (step : ∀ x p, s.parent.get x = some p → P p → P x)
    (x : Fin n) : P x :=
  Forest.induction_on_parent s.acyclic base step x

-- -----------------------------------------------------------------------------
-- Well-Foundedness Logic (The "Forest" invariant)
-- -----------------------------------------------------------------------------

/--
Proves that grafting a tree onto a root preserves well-foundedness.
General version working on an arbitrary type `α`.

This lemma shows that if we have a well-founded parent relation (a forest) and we
reparent a single node `x` to `root`, the relation remains well-founded provided
that `root` was already a root and `x ≠ root`.

Arguments:
- `parent`: The original parent function mapping a node to its parent (or `none`).
- `wf`: A proof that the relation defined by `parent` is well-founded.
- `x`: The node whose parent is being updated.
- `root`: The new parent for node `x`.
- `h_root`: A proof that `root` is currently a root (has no parent) in `parent`.
- `h_neq`: A proof that `x` and `root` are distinct, preventing a self-loop.
- `parent'`: The updated parent function.
- `h_set`: A proof that `parent' x = some root`.
- `h_other`: A proof that for all other nodes `i ≠ x`, `parent' i = parent i`.

The logic is that any path in the new relation either:
1. Never encounters `x`, thus remaining well-founded by the original relation.
2. Encounters `x`, then moves to `root`, and terminates because `root` is a root.
-/
lemma wf_graft_to_root_by_parts {α : Type}
    (parent : α → Option α)
    (wf : WellFounded (ParentRel parent))
    (x root : α)
    (h_root : parent root = none)
    (h_neq : x ≠ root)
    (parent' : α → Option α)
    (h_set : parent' x = some root)
    (h_other : ∀ i, i ≠ x → parent' i = parent i)
    : WellFounded (ParentRel parent') := by
  let rel' := ParentRel parent'
  apply WellFounded.intro; intro a
  have h_root_acc : Acc rel' root := by
    apply Acc.intro; intro c hc; dsimp [rel'] at hc
    rw [ParentRel, h_other root (Ne.symm h_neq), h_root] at hc
    simp_all
  apply Forest.induction_on_parent wf (P := fun k => Acc rel' k)
  case' h.base => intro a ha
  case' h.step => intro a p ha ih
  all_goals
    apply Acc.intro
    intro b hb
    dsimp [rel'] at hb
    if hax : a = x then subst hax; rw [ParentRel, h_set] at hb; simp_all
    else rw [ParentRel, h_other a hax, ha] at hb; simp_all

/--
Specific version of `wf_graft_to_root_by_parts` for the `Forest` structure.
Shows that updating a root's parent to another root keeps the forest acyclic.
-/
lemma wf_graft_to_root {n : ℕ} (f : Forest n) (x root: Fin n)
    (h_root: f.parent.get root = none) (h_neq: x ≠ root) :
    let parent' := f.parent.set x (some root)
    WellFounded (ParentRel (fun i => parent'.get i)) :=
  wf_graft_to_root_by_parts (fun i => f.parent.get i) f.acyclic x root h_root h_neq
    (fun i => (f.parent.set x (some root)).get i)
    (ArrayN.get_set_eq f.parent x (some root))
    (fun i h => ArrayN.get_set_ne f.parent x i (some root) (Ne.symm h))

-- -----------------------------------------------------------------------------
-- Primitive Mutation: GRAFT
-- Attaches a root 'x' to another root 'root'. Updates rank.
-- -----------------------------------------------------------------------------

/--
Attaches the tree rooted at `x` to the root `root`.
This is a core operation in Union-Find.
Note: This low-level operation does NOT update the rank. Rank updates are handled by the Union policy.
-/
def Forest.graft {n : ℕ} (f : Forest n) (x root : Fin n)
    (h_root : f.isRoot root)
    (h_neq : x ≠ root) : Forest n :=
  let nu_parent := f.parent.set x (some root)
  { f with
    parent := nu_parent,
    acyclic := wf_graft_to_root f x root h_root h_neq
  }
