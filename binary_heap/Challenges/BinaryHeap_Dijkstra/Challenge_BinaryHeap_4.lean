/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

set_option autoImplicit true

-- decrease_priority_correctness:
-- States the two main correctness properties of `decrease_priority`:
-- - Membership preservation/behavior: an element `v` is in the original tree
--   exactly when it is in the tree after calling `decrease_priority bt v' f`.
--   In other words, decreasing the priority does not lose or create elements.
-- - Heap preservation: if the original `bt` is a min-heap, then decreasing
--   the priority of a value preserves the min-heap property.
-- The proof combines the containment lemmas and the preservation lemma above.
namespace BinaryHeapChallenge4Helpers
open BinaryTree
private lemma containsb_eq_true_iff_contains {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x : α), containsb t x = true ↔ contains t x := by
  intro t x
  induction t with
  | leaf => simp [containsb, contains]
  | node l v r ihl ihr => simp [containsb, contains, ihl, ihr]


private lemma contains_insert_iff {α : Type u} :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (BinaryTree.insert t y f) x ↔ contains t x ∨ x = y := by
  intro t x y f
  induction t generalizing y with
  | leaf =>
      simp only [BinaryTree.insert, contains, Bool.false_eq_true, or_self, or_false, false_or]
      exact eq_comm
  | node l v r ihl ihr =>
      by_cases h : f y ≤ f v
      · simp only [BinaryTree.insert, h, ↓reduceIte, contains, ihl]
        tauto
      · simp only [BinaryTree.insert, h, ↓reduceIte, contains, ihl]
        tauto


private lemma contains_merge_iff {α : Type u} :
    ∀ (t₁ t₂ : BinaryTree α) (x : α) (f : α → ENat),
      contains (merge t₁ t₂ f) x ↔ contains t₁ x ∨ contains t₂ x := by
  intro t₁ t₂ x f
  fun_induction merge t₁ t₂ f <;>
    simp only [contains, Bool.false_eq_true, false_or, or_false, *] <;> aesop


private lemma contains_remove_subset {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (remove t y f) x → contains t x := by
  intro t x y f
  induction t generalizing y f with
  | leaf => simp [remove, contains]
  | node l v r ihl ihr =>
      by_cases h : y = v
      · subst h
        simp [remove, contains, contains_merge_iff]
        intro hcase
        exact Or.inr hcase
      · simp [remove, contains, h]
        intro hcase
        rcases hcase with hroot | hl | hr
        · exact Or.inl hroot
        · exact Or.inr (Or.inl (ihl y f hl))
        · exact Or.inr (Or.inr (ihr y f hr))


private lemma contains_remove_of_ne {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains t x → x ≠ y → contains (remove t y f) x := by
  intro t x y f
  induction t generalizing y f with
  | leaf => simp [contains]
  | node l v r ihl ihr =>
      intro hmem hne
      by_cases h : y = v
      · subst h
        simp [remove, contains_merge_iff]
        rcases hmem with hvx | hl | hr
        · exact False.elim (hne hvx.symm)
        · exact Or.inl hl
        · exact Or.inr hr
      · simp [remove, h, contains]
        rcases hmem with hvx | hl | hr
        · exact Or.inl hvx
        · exact Or.inr (Or.inl (ihl y f hl hne))
        · exact Or.inr (Or.inr (ihr y f hr hne))


private lemma contains_decrease_priority_iff {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (decrease_priority t y f) x ↔ contains t x := by
  intro t x y f
  by_cases hy : containsb t y = true
  · have hymem : contains t y := (containsb_eq_true_iff_contains t y).mp hy
    simp [decrease_priority, hy, contains_insert_iff]
    constructor
    · intro h
      rcases h with hrem | hxy
      · exact contains_remove_subset t x y f hrem
      · simpa [hxy] using hymem
    · intro hx
      by_cases hxy : x = y
      · exact Or.inr hxy
      · exact Or.inl (contains_remove_of_ne t x y f hx hxy)
  · simp [decrease_priority, hy]


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
      simp only [BinaryTree.insert, StrongHeap, and_self, and_true]
      intro x hx
      cases hx
  | node l v r ihl ihr =>
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      by_cases h : f y ≤ f v
      · simp only [BinaryTree.insert, h, ↓reduceIte, StrongHeap]
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
      · simp only [BinaryTree.insert, h, ↓reduceIte, StrongHeap]
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


private lemma strongHeap_merge {α : Type u} :
    ∀ (t₁ t₂ : BinaryTree α) (f : α → ENat),
      StrongHeap t₁ f → StrongHeap t₂ f → StrongHeap (merge t₁ t₂ f) f := by
  intro t₁ t₂ f h₁ h₂
  fun_induction merge t₁ t₂ f with
  | case1 t => simpa [merge] using h₂
  | case2 t => simpa [merge] using h₁
  | case3 l1 v1 r1 l2 v2 r2 hle ih =>
      rcases h₁ with ⟨hl1, hr1, hhl1, hhr1⟩
      have h₂root : ∀ x, contains (node l2 v2 r2) x → f v2 ≤ f x := by
        intro x hx
        exact strongHeap_root_le h₂ hx
      simp only [StrongHeap]
      constructor
      · intro x hx
        have hx' := (contains_merge_iff l1 (node l2 v2 r2) x f).mp hx
        rcases hx' with hxl1 | hx2
        · exact hl1 x hxl1
        · exact le_trans hle (h₂root x hx2)
      · constructor
        · exact hr1
        · constructor
          · exact ih hhl1 h₂
          · exact hhr1
  | case4 l1 v1 r1 l2 v2 r2 hnot ih =>
      rcases h₂ with ⟨hl2, hr2, hhl2, hhr2⟩
      have hle : f v2 ≤ f v1 := le_of_not_ge hnot
      have h₁root : ∀ x, contains (node l1 v1 r1) x → f v1 ≤ f x := by
        intro x hx
        exact strongHeap_root_le h₁ hx
      simp only [StrongHeap]
      constructor
      · intro x hx
        have hx' := (contains_merge_iff (node l1 v1 r1) l2 x f).mp hx
        rcases hx' with hx1 | hxl2
        · exact le_trans hle (h₁root x hx1)
        · exact hl2 x hxl2
      · constructor
        · exact hr2
        · constructor
          · exact ih h₁ hhl2
          · exact hhr2


private lemma strongHeap_remove {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      StrongHeap t f → StrongHeap (remove t y f) f := by
  intro t y f hheap
  induction t generalizing y f with
  | leaf => simp [remove, StrongHeap]
  | node l v r ihl ihr =>
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      by_cases hy : y = v
      · subst hy
        simp [remove]
        exact strongHeap_merge l r f hhl hhr
      · simp [remove, hy, StrongHeap]
        constructor
        · intro x hx
          exact hl x (contains_remove_subset l x y f hx)
        · constructor
          · intro x hx
            exact hr x (contains_remove_subset r x y f hx)
          · constructor
            · exact ihl y f hhl
            · exact ihr y f hhr
end BinaryHeapChallenge4Helpers

namespace BinaryHeapChallenge4Helpers
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

private lemma strongHeap_decrease_priority_same {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      StrongHeap t f → StrongHeap (decrease_priority t y f) f := by
  intro t y f hheap
  by_cases hy : containsb t y = true
  · simp [decrease_priority, hy]
    exact strongHeap_insert (remove t y f) y f (strongHeap_remove t y f hheap)
  · simp [decrease_priority, hy, hheap]

end BinaryHeapChallenge4Helpers

open BinaryHeapChallenge4Helpers

lemma decrease_priority_correctness [DecidableEq α] (bt: BinaryTree α) (v v': α) (f : α → ENat):
  contains bt v ↔ contains (decrease_priority bt v' f) v ∧
  (is_min_heap bt f → is_min_heap (decrease_priority bt v f) f) := by
  constructor
  · intro hmem
    constructor
    · exact (contains_decrease_priority_iff bt v v' f).2 hmem
    · intro hmin
      exact is_min_heap_of_strongHeap (decrease_priority bt v f) f
        (strongHeap_decrease_priority_same bt v f
          (strongHeap_of_is_min_heap bt f hmin))
  · intro h
    exact (contains_decrease_priority_iff bt v v' f).1 h.1
