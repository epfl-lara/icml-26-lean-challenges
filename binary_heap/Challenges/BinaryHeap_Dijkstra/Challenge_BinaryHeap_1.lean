/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

set_option autoImplicit true

-- heapify_correctness:
-- This theorem bundles two key correctness properties of `heapify`:
-- 1) `heapify` preserves membership: an element is contained in `heapify bt f`
--    iff it was contained in `bt`.
-- 2) If `bt = node l v r` and both children `l` and `r` are min-heaps, then
--    `heapify bt f` is a min-heap. The proof combines containment lemmas and
--    `heapify_establishes_min_heap` which shows that fixing one violating
--    child yields a valid min-heap.
namespace BinaryHeapChallenge1Helpers
open BinaryTree
private lemma contains_heapify_iff {α : Type u} :
    ∀ (t : BinaryTree α) (x : α) (f : α → ENat),
      contains (heapify t f) x ↔ contains t x := by
  intro t x f
  fun_induction heapify t f <;> simp only [contains, *] <;> aesop


private def StrongHeap : BinaryTree α → (α → ENat) → Prop
  | leaf, _ => True
  | node l v r, f =>
      (∀ x, contains l x → f v ≤ f x) ∧
      (∀ x, contains r x → f v ≤ f x) ∧
      StrongHeap l f ∧ StrongHeap r f


private def ChildrenStrongHeap : BinaryTree α → (α → ENat) → Prop
  | leaf, _ => True
  | node l _ r, f => StrongHeap l f ∧ StrongHeap r f


private lemma strongHeap_root_le {α : Type u} {l r : BinaryTree α} {v x : α} {f : α → ENat} :
    StrongHeap (node l v r) f → contains (node l v r) x → f v ≤ f x := by
  intro hheap hmem
  rcases hheap with ⟨hl, hr, hhl, hhr⟩
  rcases hmem with hvx | hx | hx
  · simp [hvx]
  · exact hl x hx
  · exact hr x hx


private lemma strongHeap_heapify {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      ChildrenStrongHeap t f → StrongHeap (heapify t f) f := by
  intro t f hch
  fun_induction heapify t f with
  | case1 => simp [StrongHeap]
  | case2 v =>
      simp [heapify, StrongHeap]
      intro x hx
      cases hx
  | case3 v rl rv rr h ih =>
      rcases hch with ⟨_, hright⟩
      rcases hright with ⟨hrl, hrr, hhrl, hhrr⟩
      simp [heapify, h, StrongHeap]
      constructor
      · intro x hx; cases hx
      · constructor
        · intro x hx
          have hxold := (contains_heapify_iff (node rl v rr) x f).mp hx
          rcases hxold with hvx | hxl | hxr
          · exact le_of_lt (by simpa [hvx] using h)
          · exact hrl x hxl
          · exact hrr x hxr
        · exact ih ⟨hhrl, hhrr⟩
  | case4 v rl rv rr h =>
      rcases hch with ⟨_, hright⟩
      rcases hright with ⟨hrl, hrr, hhrl, hhrr⟩
      have hvle : f v ≤ f rv := le_of_not_gt h
      simp [heapify, h, StrongHeap]
      constructor
      · intro x hx; cases hx
      · constructor
        · intro x hx
          rcases hx with hvx | hrest
          · simpa [hvx] using hvle
          · rcases hrest with hxl | hxr
            · exact le_trans hvle (hrl x hxl)
            · exact le_trans hvle (hrr x hxr)
        · exact ⟨hrl, hrr, hhrl, hhrr⟩
  | case5 v ll lv lr h ih =>
      rcases hch with ⟨hleft, _⟩
      rcases hleft with ⟨hll, hlr, hhll, hhlr⟩
      simp [heapify, h, StrongHeap]
      constructor
      · intro x hx
        have hxold := (contains_heapify_iff (node ll v lr) x f).mp hx
        rcases hxold with hvx | hxl | hxr
        · exact le_of_lt (by simpa [hvx] using h)
        · exact hll x hxl
        · exact hlr x hxr
      · constructor
        · intro x hx; cases hx
        · exact ih ⟨hhll, hhlr⟩
  | case6 v ll lv lr h =>
      rcases hch with ⟨hleft, _⟩
      rcases hleft with ⟨hll, hlr, hhll, hhlr⟩
      have hvle : f v ≤ f lv := le_of_not_gt h
      simp [heapify, h, StrongHeap]
      constructor
      · intro x hx
        rcases hx with hvx | hrest
        · simpa [hvx] using hvle
        · rcases hrest with hxl | hxr
          · exact le_trans hvle (hll x hxl)
          · exact le_trans hvle (hlr x hxr)
      · constructor
        · intro x hx; cases hx
        · exact ⟨hll, hlr, hhll, hhlr⟩
  | case7 v ll lv lr rl rv rr hlerv hvle =>
      rcases hch with ⟨hl, hr⟩
      simp [heapify, hlerv, hvle, StrongHeap]
      constructor
      · intro x hx
        exact le_trans hvle (strongHeap_root_le hl hx)
      · constructor
        · intro x hx
          exact le_trans (le_trans hvle hlerv) (strongHeap_root_le hr hx)
        · exact ⟨hl, hr⟩
  | case8 v ll lv lr rl rv rr hlerv hlt ih =>
      rcases hch with ⟨hl, hr⟩
      rcases hl with ⟨hll, hlr, hhll, hhlr⟩
      simp [heapify, hlerv, hlt, StrongHeap]
      constructor
      · intro x hx
        have hxold := (contains_heapify_iff (node ll v lr) x f).mp hx
        rcases hxold with hvx | hxl | hxr
        · exact le_of_lt (by simpa [hvx] using hlt)
        · exact hll x hxl
        · exact hlr x hxr
      · constructor
        · intro x hx
          exact le_trans hlerv (strongHeap_root_le hr hx)
        · constructor
          · exact ih ⟨hhll, hhlr⟩
          · exact hr
  | case9 v ll lv lr rl rv rr hnot hvle =>
      rcases hch with ⟨hl, hr⟩
      have hrvlelv : f rv ≤ f lv := le_of_lt (lt_of_not_ge hnot)
      simp [heapify, hnot, hvle, StrongHeap]
      constructor
      · intro x hx
        exact le_trans (le_trans hvle hrvlelv) (strongHeap_root_le hl hx)
      · constructor
        · intro x hx
          exact le_trans hvle (strongHeap_root_le hr hx)
        · exact ⟨hl, hr⟩
  | case10 v ll lv lr rl rv rr hnot hrvvlt ih =>
      rcases hch with ⟨hl, hr⟩
      rcases hr with ⟨hrl, hrr, hhrl, hhrr⟩
      have hrvlelv : f rv ≤ f lv := le_of_lt (lt_of_not_ge hnot)
      simp [heapify, hnot, hrvvlt, StrongHeap]
      constructor
      · intro x hx
        exact le_trans hrvlelv (strongHeap_root_le hl hx)
      · constructor
        · intro x hx
          have hxold := (contains_heapify_iff (node rl v rr) x f).mp hx
          rcases hxold with hvx | hxl | hxr
          · exact le_of_lt (by simpa [hvx] using hrvvlt)
          · exact hrl x hxl
          · exact hrr x hxr
        · constructor
          · exact hl
          · exact ih ⟨hhrl, hhrr⟩
end BinaryHeapChallenge1Helpers

namespace BinaryHeapChallenge1Helpers
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

end BinaryHeapChallenge1Helpers

open BinaryHeapChallenge1Helpers

theorem heapify_correctness (bt: BinaryTree α) (f: α → ENat):
  (contains (heapify bt f) v ↔ contains bt v) ∧
  bt = node l v r ∧ is_min_heap l f ∧ is_min_heap r f → is_min_heap (heapify bt f) f := by
  intro h
  rcases h with ⟨_, hnode, hl, hr⟩
  subst bt
  exact is_min_heap_of_strongHeap (heapify (node l v r) f) f
    (strongHeap_heapify (node l v r) f
      ⟨strongHeap_of_is_min_heap l f hl, strongHeap_of_is_min_heap r f hr⟩)
