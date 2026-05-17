/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

-- insert_correctness:
-- Describes the behavior of `insert`:
-- - Membership: inserting `v'` into `bt` yields a tree where an element `v`
--   is present iff it was already in `bt` or `v = v'` (no elements are lost,
--   and the new element is present).
-- - Heap preservation: if `bt` is a min-heap, then inserting preserves the
--   min-heap property.  The proof follows by structural induction on `insert`
--   and uses `min_heap*` lemmas to maintain the root ordering.
private def heapRootLe {α : Type u} (f : α → ENat) (p : ENat) : BinaryTree α → Prop
  | leaf => True
  | node _ v _ => p ≤ f v

private theorem is_min_heap_left_of_node {α : Type u} {f : α → ENat}
    {l r : BinaryTree α} {v : α} :
    is_min_heap (node l v r) f → is_min_heap l f := by
  cases l with
  | leaf =>
      cases r <;> simp [is_min_heap]
  | node ll lv lr =>
      cases r with
      | leaf =>
          intro h
          exact h.2
      | node rl rv rr =>
          intro h
          exact h.2.1

private theorem is_min_heap_right_of_node {α : Type u} {f : α → ENat}
    {l r : BinaryTree α} {v : α} :
    is_min_heap (node l v r) f → is_min_heap r f := by
  cases r with
  | leaf =>
      cases l <;> simp [is_min_heap]
  | node rl rv rr =>
      cases l with
      | leaf =>
          intro h
          exact h.2
      | node ll lv lr =>
          intro h
          exact h.2.2.2

private theorem heapRootLe_mono {α : Type u} {f : α → ENat}
    {p q : ENat} {bt : BinaryTree α} :
    p ≤ q → heapRootLe f q bt → heapRootLe f p bt := by
  intro hpq hq
  cases bt with
  | leaf =>
      simp [heapRootLe]
  | node l v r =>
      exact le_trans hpq hq

private theorem heapRootLe_left_of_min_heap {α : Type u} {f : α → ENat}
    {l r : BinaryTree α} {v : α} :
    is_min_heap (node l v r) f → heapRootLe f (f v) l := by
  cases l with
  | leaf =>
      cases r <;> simp [heapRootLe]
  | node ll lv lr =>
      cases r with
      | leaf =>
          intro h
          exact h.1
      | node rl rv rr =>
          intro h
          exact h.1

private theorem heapRootLe_right_of_min_heap {α : Type u} {f : α → ENat}
    {l r : BinaryTree α} {v : α} :
    is_min_heap (node l v r) f → heapRootLe f (f v) r := by
  cases r with
  | leaf =>
      cases l <;> simp [heapRootLe]
  | node rl rv rr =>
      cases l with
      | leaf =>
          intro h
          exact h.1
      | node ll lv lr =>
          intro h
          exact h.2.2.1

private theorem is_min_heap_node_of_rootLe {α : Type u} {f : α → ENat}
    {l r : BinaryTree α} {v : α} :
    is_min_heap l f → is_min_heap r f →
    heapRootLe f (f v) l → heapRootLe f (f v) r →
    is_min_heap (node l v r) f := by
  intro hl hr hleft hright
  cases l with
  | leaf =>
      cases r with
      | leaf =>
          simp [is_min_heap]
      | node rl rv rr =>
          simpa [is_min_heap, heapRootLe] using And.intro hright hr
  | node ll lv lr =>
      cases r with
      | leaf =>
          simpa [is_min_heap, heapRootLe] using And.intro hleft hl
      | node rl rv rr =>
          simpa [is_min_heap, heapRootLe] using And.intro hleft (And.intro hl (And.intro hright hr))

private theorem contains_insert {α : Type u} (bt : BinaryTree α) (f : α → ENat) :
    ∀ v v' : α, contains (insert bt v' f) v ↔ contains bt v ∨ v = v' := by
  induction bt with
  | leaf =>
      intro v v'
      simp [BinaryTree.insert, BinaryTree.contains]
      constructor <;> intro h <;> exact h.symm
  | node l x r ihl ihr =>
      intro v v'
      by_cases hle : f v' ≤ f x
      · simp [BinaryTree.insert, BinaryTree.contains, hle, ihl, eq_comm, or_assoc, or_left_comm, or_comm]
      · simp [BinaryTree.insert, BinaryTree.contains, hle, ihl, or_assoc, or_left_comm, or_comm]

private theorem insert_heap_correct_aux {α : Type u} (bt : BinaryTree α) (f : α → ENat) :
    ∀ v : α, is_min_heap bt f →
      is_min_heap (insert bt v f) f ∧
        ∀ p, heapRootLe f p bt → p ≤ f v → heapRootLe f p (insert bt v f) := by
  induction bt with
  | leaf =>
      intro v hheap
      constructor
      · simp [BinaryTree.insert, is_min_heap]
      · intro p hpbt hpv
        simpa [BinaryTree.insert, heapRootLe] using hpv
  | node l x r ihl ihr =>
      intro v hheap
      have hl : is_min_heap l f :=
        is_min_heap_left_of_node (f := f) (l := l) (v := x) (r := r) hheap
      have hr : is_min_heap r f :=
        is_min_heap_right_of_node (f := f) (l := l) (v := x) (r := r) hheap
      constructor
      · by_cases hle : f v ≤ f x
        · have recX := ihl x hl
          have hleftRootX : heapRootLe f (f x) l :=
            heapRootLe_left_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap
          have hrightRootX : heapRootLe f (f x) r :=
            heapRootLe_right_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap
          have hleftRoot : heapRootLe f (f v) (insert l x f) :=
            recX.2 (f v) (heapRootLe_mono (f := f) hle hleftRootX) hle
          have hrightRoot : heapRootLe f (f v) r :=
            heapRootLe_mono (f := f) hle hrightRootX
          simpa [BinaryTree.insert, hle] using
            (is_min_heap_node_of_rootLe (f := f) (l := insert l x f) (r := r) (v := v)
              recX.1 hr hleftRoot hrightRoot)
        · have hxv : f x ≤ f v := le_of_lt (lt_of_not_ge hle)
          have recV := ihl v hl
          have hleftRootX : heapRootLe f (f x) l :=
            heapRootLe_left_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap
          have hrightRoot : heapRootLe f (f x) r :=
            heapRootLe_right_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap
          have hleftRoot : heapRootLe f (f x) (insert l v f) :=
            recV.2 (f x) hleftRootX hxv
          simpa [BinaryTree.insert, hle] using
            (is_min_heap_node_of_rootLe (f := f) (l := insert l v f) (r := r) (v := x)
              recV.1 hr hleftRoot hrightRoot)
      · intro p hpbt hpv
        by_cases hle : f v ≤ f x
        · simpa [BinaryTree.insert, hle, heapRootLe] using hpv
        · have hpx : p ≤ f x := by
            simpa [heapRootLe] using hpbt
          simpa [BinaryTree.insert, hle, heapRootLe] using hpx

theorem insert_correctness (bt: BinaryTree α) (f: α → ENat):
  (∀ v v', contains bt v ∨ v = v' ↔ contains (insert bt v' f) v)
  ∧ (is_min_heap bt f → is_min_heap (insert bt v f) f) := by
  constructor
  · intro v v'
    exact (contains_insert bt f v v').symm
  · intro hheap
    exact (insert_heap_correct_aux bt f v hheap).1
