/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

set_option autoImplicit true

-- insert_correctness:
-- Describes the behavior of `insert`:
-- - Membership: inserting `v'` into `bt` yields a tree where an element `v`
--   is present iff it was already in `bt` or `v = v'` (no elements are lost,
--   and the new element is present).
-- - Heap preservation: if `bt` is a min-heap, then inserting preserves the
--   min-heap property.  The proof follows by structural induction on `insert`
--   and uses `min_heap*` lemmas to maintain the root ordering.
namespace BinaryHeapChallenge3Helpers
open BinaryTree
private lemma contains_insert_iff {α : Type u} :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (BinaryTree.insert t y f) x ↔ contains t x ∨ x = y := by
  intro t x y f
  induction t generalizing y with
  | leaf =>
      simp [BinaryTree.insert, contains]
      exact eq_comm
  | node l v r ihl ihr =>
      by_cases h : f y ≤ f v
      · simp [BinaryTree.insert, contains, h, ihl]
        grind
      · simp [BinaryTree.insert, contains, h, ihl]
        grind


private def StrongHeap : BinaryTree α → (α → ENat) → Prop
  | leaf, _ => True
  | node l v r, f =>
      (∀ x, contains l x → f v ≤ f x) ∧
      (∀ x, contains r x → f v ≤ f x) ∧
      StrongHeap l f ∧ StrongHeap r f


private lemma strongHeap_root_le {α : Type u} {l r : BinaryTree α} {v x : α} {f : α → ENat} :
    StrongHeap (node l v r) f → contains (node l v r) x → f v ≤ f x := by
  intro hheap hmem
  rcases hheap with ⟨hl, hr, hhl, hhr⟩
  rcases hmem with hvx | hx | hx
  · simp [hvx]
  · exact hl x hx
  · exact hr x hx


private lemma strongHeap_insert {α : Type u} :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      StrongHeap t f → StrongHeap (BinaryTree.insert t y f) f := by
  intro t y f hheap
  induction t generalizing y with
  | leaf =>
      simp [BinaryTree.insert, StrongHeap]
      intro x hx
      cases hx
  | node l v r ihl ihr =>
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      by_cases h : f y ≤ f v
      · simp [BinaryTree.insert, h, StrongHeap]
        constructor
        · intro x hx
          have hx' := (contains_insert_iff l x v f).mp hx
          rcases hx' with hxl | hxv
          · exact le_trans h (hl x hxl)
          · simpa [hxv] using h
        · constructor
          · intro x hx
            exact le_trans h (hr x hx)
          · constructor
            · exact ihl v hhl
            · exact hhr
      · simp [BinaryTree.insert, h, StrongHeap]
        constructor
        · intro x hx
          have hx' := (contains_insert_iff l x y f).mp hx
          rcases hx' with hxl | hxy
          · exact hl x hxl
          · have hy_ge : f v ≤ f y := by exact le_of_not_ge h
            simpa [hxy] using hy_ge
        · constructor
          · exact hr
          · constructor
            · exact ihl y hhl
            · exact hhr
end BinaryHeapChallenge3Helpers

namespace BinaryHeapChallenge3Helpers
open BinaryTree

private lemma strongHeap_of_is_min_heap {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat), is_min_heap t f → StrongHeap t f := by
  intro t f h
  induction t with
  | leaf =>
      change True
      trivial
  | node l v r ihl ihr =>
      change (∀ x, contains l x → f v ≤ f x) ∧
        (∀ x, contains r x → f v ≤ f x) ∧
        StrongHeap l f ∧ StrongHeap r f
      cases l with
      | leaf =>
          cases r with
          | leaf =>
              constructor
              · intro x hx; cases hx
              · constructor
                · intro x hx; cases hx
                · exact ⟨trivial, trivial⟩
          | node rl rv rr =>
              change f v ≤ f rv ∧ is_min_heap (node rl rv rr) f at h
              rcases h with ⟨hvr, hr⟩
              have hsr := ihr hr
              constructor
              · intro x hx; cases hx
              · constructor
                · intro x hx
                  exact le_trans hvr (strongHeap_root_le hsr hx)
                · exact ⟨trivial, hsr⟩
      | node ll lv lr =>
          cases r with
          | leaf =>
              change f v ≤ f lv ∧ is_min_heap (node ll lv lr) f at h
              rcases h with ⟨hvl, hl⟩
              have hsl := ihl hl
              constructor
              · intro x hx
                exact le_trans hvl (strongHeap_root_le hsl hx)
              · constructor
                · intro x hx; cases hx
                · exact ⟨hsl, trivial⟩
          | node rl rv rr =>
              change f v ≤ f lv ∧ is_min_heap (node ll lv lr) f ∧
                f v ≤ f rv ∧ is_min_heap (node rl rv rr) f at h
              rcases h with ⟨hvl, hl, hvr, hr⟩
              have hsl := ihl hl
              have hsr := ihr hr
              constructor
              · intro x hx
                exact le_trans hvl (strongHeap_root_le hsl hx)
              · constructor
                · intro x hx
                  exact le_trans hvr (strongHeap_root_le hsr hx)
                · exact ⟨hsl, hsr⟩

private lemma is_min_heap_of_strongHeap {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat), StrongHeap t f → is_min_heap t f := by
  intro t f h
  induction t with
  | leaf =>
      simp [is_min_heap]
  | node l v r ihl ihr =>
      rcases h with ⟨hl, hr, hsl, hsr⟩
      cases l with
      | leaf =>
          cases r with
          | leaf =>
              simp [is_min_heap]
          | node rl rv rr =>
              change f v ≤ f rv ∧ is_min_heap (node rl rv rr) f
              exact ⟨hr rv (Or.inl rfl), ihr hsr⟩
      | node ll lv lr =>
          cases r with
          | leaf =>
              change f v ≤ f lv ∧ is_min_heap (node ll lv lr) f
              exact ⟨hl lv (Or.inl rfl), ihl hsl⟩
          | node rl rv rr =>
              change f v ≤ f lv ∧ is_min_heap (node ll lv lr) f ∧
                f v ≤ f rv ∧ is_min_heap (node rl rv rr) f
              exact ⟨hl lv (Or.inl rfl), ihl hsl, hr rv (Or.inl rfl), ihr hsr⟩

end BinaryHeapChallenge3Helpers

open BinaryHeapChallenge3Helpers

theorem insert_correctness (bt: BinaryTree α) (f: α → ENat):
  (∀ v v', contains bt v ∨ v = v' ↔ contains (insert bt v' f) v)
  ∧ (is_min_heap bt f → is_min_heap (insert bt v f) f) := by
  constructor
  · intro v v'
    exact (contains_insert_iff bt v v' f).symm
  · intro hmin
    exact is_min_heap_of_strongHeap (insert bt v f) f
      (strongHeap_insert bt v f (strongHeap_of_is_min_heap bt f hmin))
