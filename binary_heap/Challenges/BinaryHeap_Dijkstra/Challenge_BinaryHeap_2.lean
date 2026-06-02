/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

set_option autoImplicit true

-- extract_min_correctness:
-- correctness for `extract_min`:
-- - The members remain the same except for the extracted minimum.
-- - If the input was a min-heap, extracting returns some value `v'` and a
--   resulting tree that is a min-heap; furthermore the extracted priority
--   equals `heap_min bt f`.
-- The proof composes containment lemmas, `get_last` properties and
-- `heapify` correctness used in `extract_min_correct_node`.
namespace BinaryHeapChallenge2Helpers
open BinaryTree
private lemma contains_heapify_iff {α : Type u} :
    ∀ (t : BinaryTree α) (x : α) (f : α → ENat),
      contains (heapify t f) x ↔ contains t x := by
  intro t x f
  fun_induction heapify t f <;> simp [heapify, contains, *] <;> grind


private lemma get_last_fst_isSome {α : Type u} :
    ∀ t : BinaryTree α, t ≠ leaf → (get_last t).1.isSome := by
  intro t ht
  induction t with
  | leaf => contradiction
  | node l v r ihl ihr =>
      cases l with
      | leaf =>
          cases r with
          | leaf => simp [get_last]
          | node rl rv rr =>
              have hne : node rl rv rr ≠ (leaf : BinaryTree α) := by intro h; cases h
              simpa [get_last] using ihr hne
      | node ll lv lr =>
          have hne : node ll lv lr ≠ (leaf : BinaryTree α) := by intro h; cases h
          simpa [get_last] using ihl hne


private lemma get_last_value_contains {α : Type u} :
    ∀ (t : BinaryTree α) (x : α), (get_last t).1 = some x → contains t x := by
  intro t x h
  fun_induction get_last t <;> simp [get_last, contains] at h ⊢ <;> grind


private lemma get_last_tree_subset {α : Type u} :
    ∀ (t : BinaryTree α) (x : α), contains (get_last t).2 x → contains t x := by
  intro t x h
  fun_induction get_last t <;> simp [get_last, contains] at h ⊢ <;> grind


private lemma get_last_value_or_tree {α : Type u} :
    ∀ (t : BinaryTree α) (x : α),
      contains t x → (get_last t).1 = some x ∨ contains (get_last t).2 x := by
  intro t x h
  fun_induction get_last t <;> simp [get_last, contains] at h ⊢ <;> grind


private lemma get_last_node_leaf_fst {α : Type u} :
    ∀ (l r : BinaryTree α) (v : α),
      (get_last (node l v r)).2 = leaf → (get_last (node l v r)).1 = some v := by
  intro l r v h
  cases l <;> cases r <;> simp [get_last] at h ⊢


private lemma get_last_node_tree_root {α : Type u} :
    ∀ (l r tl tr : BinaryTree α) (v tv : α),
      (get_last (node l v r)).2 = node tl tv tr → tv = v := by
  intro l r tl tr v tv h
  cases l <;> cases r <;> simp [get_last] at h ⊢ <;> grind


private lemma extract_min_fst_node {α : Type u} :
    ∀ (l r : BinaryTree α) (v : α) (f : α → ENat),
      (extract_min (node l v r) f).1 = some v := by
  intro l r v f
  cases l with
  | leaf =>
      cases r with
      | leaf => simp [extract_min, get_last]
      | node rl rv rr =>
          unfold extract_min
          simp only [get_last]
          change (match (get_last (node rl rv rr)).1 with
            | none => (none, leaf)
            | some v' => (some v, (node leaf v' (get_last (node rl rv rr)).2).heapify f)).1 =
              some v
          have hs := get_last_fst_isSome (node rl rv rr) (by intro h; cases h)
          cases hlast : get_last (node rl rv rr) with
          | mk o t =>
              cases o with
              | none => simp [hlast] at hs
              | some a => simp
  | node ll lv lr =>
      unfold extract_min
      simp only [get_last]
      change (match (get_last (node ll lv lr)).1 with
        | none => (none, leaf)
        | some v' => (some v, (node (get_last (node ll lv lr)).2 v' r).heapify f)).1 =
          some v
      have hs := get_last_fst_isSome (node ll lv lr) (by intro h; cases h)
      cases hlast : get_last (node ll lv lr) with
      | mk o t =>
          cases o with
          | none => simp [hlast] at hs
          | some a => simp


private lemma contains_extract_min_subset {α : Type u} :
    ∀ (t : BinaryTree α) (x : α) (f : α → ENat),
      contains (extract_min t f).2 x → contains t x := by
  intro t x f hmem
  unfold extract_min at hmem
  cases hlast : get_last t with
  | mk o rest =>
      simp [hlast] at hmem
      cases o with
      | none => simp [contains] at hmem
      | some last =>
          cases hrest : rest with
          | leaf => simp [hrest, contains] at hmem
          | node l v r =>
              have hpre : contains (node l last r) x := by
                exact (contains_heapify_iff (node l last r) x f).mp (by simpa [hrest] using hmem)
              rcases hpre with hlastx | hl | hr
              · exact get_last_value_contains t x (by simpa [hlastx] using congrArg Prod.fst hlast)
              · exact get_last_tree_subset t x (by
                  rw [hlast, hrest]
                  simp [contains]
                  exact Or.inr (Or.inl hl))
              · exact get_last_tree_subset t x (by
                  rw [hlast, hrest]
                  simp [contains]
                  exact Or.inr (Or.inr hr))


private lemma contains_extract_min_of_ne_root {α : Type u} :
    ∀ (l r : BinaryTree α) (root x : α) (f : α → ENat),
      contains (node l root r) x → x ≠ root → contains (extract_min (node l root r) f).2 x := by
  intro l r root x f hmem hxne
  unfold extract_min
  cases hlast : get_last (node l root r) with
  | mk o t =>
      have hor := get_last_value_or_tree (node l root r) x hmem
      simp [hlast] at hor
      cases o with
      | none =>
          have hs := get_last_fst_isSome (node l root r) (by intro h; cases h)
          simp [hlast] at hs
      | some last =>
          cases ht : t with
          | leaf =>
              have hfst := get_last_node_leaf_fst l r root
              have hlast_root : last = root := by
                have := hfst (by simpa [hlast, ht])
                simpa [hlast] using this
              rcases hor with hlastx | htree
              · have : x = root := by
                  have hxlast : last = x := by simpa [hlast] using hlastx
                  exact hxlast ▸ hlast_root
                exact False.elim (hxne this)
              · rw [ht] at htree
                cases htree
          | node tl tv tr =>
              have htv : tv = root := by
                exact get_last_node_tree_root l r tl tr root tv (by simpa [hlast, ht])
              simp [ht, contains_heapify_iff, contains]
              rcases hor with hlastx | htree
              · have hxlast : last = x := by simpa [hlast] using hlastx
                exact Or.inl hxlast
              · rw [ht] at htree
                rcases htree with htvx | htl | htr
                · have : x = root := by simpa [htv] using htvx.symm
                  exact False.elim (hxne this)
                · exact Or.inr (Or.inl htl)
                · exact Or.inr (Or.inr htr)


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


private lemma strongHeap_get_last_tree {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      StrongHeap t f → StrongHeap (get_last t).2 f := by
  intro t f hheap
  fun_induction get_last t <;> simp [get_last, StrongHeap] at * <;>
    grind [get_last_tree_subset]


private lemma strongHeap_extract_min {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      StrongHeap t f → StrongHeap (extract_min t f).2 f := by
  intro t f hheap
  cases t with
  | leaf => simp [extract_min, get_last, StrongHeap]
  | node l v r =>
      unfold extract_min
      cases hlast : get_last (node l v r) with
      | mk o rest =>
          cases o with
          | none => simp [StrongHeap]
          | some last =>
              cases hrest : rest with
              | leaf => simp [StrongHeap]
              | node tl tv tr =>
                  have hrestheap : StrongHeap (node tl tv tr) f := by
                    have := strongHeap_get_last_tree (node l v r) f hheap
                    simpa [hlast, hrest] using this
                  rcases hrestheap with ⟨hl, hr, hhl, hhr⟩
                  simp [hrest]
                  exact strongHeap_heapify (node tl last tr) f ⟨hhl, hhr⟩
end BinaryHeapChallenge2Helpers

namespace BinaryHeapChallenge2Helpers
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

private lemma heap_min_eq_root_of_is_min_heap {α : Type u} :
    ∀ (l r : BinaryTree α) (v : α) (f : α → ENat),
      is_min_heap (node l v r) f → heap_min (node l v r) f = f v := by
  intro l r v f h
  cases l with
  | leaf =>
      cases r with
      | leaf => simp [heap_min]
      | node rl rv rr =>
          change f v ≤ f rv ∧ is_min_heap (node rl rv rr) f at h
          simp [heap_min, h.1]
  | node ll lv lr =>
      cases r with
      | leaf =>
          change f v ≤ f lv ∧ is_min_heap (node ll lv lr) f at h
          simp [heap_min, h.1]
      | node rl rv rr =>
          change f v ≤ f lv ∧ is_min_heap (node ll lv lr) f ∧
            f v ≤ f rv ∧ is_min_heap (node rl rv rr) f at h
          rcases h with ⟨hvl, hl, hvr, hr⟩
          by_cases hlr : f lv ≤ f rv
          · simp [heap_min, hlr, hvl]
          · simp [heap_min, hlr, hvr]

end BinaryHeapChallenge2Helpers

open BinaryHeapChallenge2Helpers

theorem extract_min_correctness (bt l r: BinaryTree α) (v v': α) (f: α → ENat): (
  contains (extract_min bt f).2 v → contains bt v)
  ∧ (bt = node l v r → contains bt v' → v ≠ v' → contains (extract_min bt f).2 v')
  ∧ (bt = node l v r → is_min_heap bt f → ∃ bt' v', extract_min bt f = (some v', bt')
  ∧ is_min_heap bt' f ∧ f v = heap_min bt f) := by
  constructor
  · intro hmem
    exact contains_extract_min_subset bt v f hmem
  · constructor
    · intro hnode hmem hne
      subst bt
      exact contains_extract_min_of_ne_root l r v v' f hmem (fun hv'v => hne hv'v.symm)
    · intro hnode hmin
      subst bt
      refine ⟨(extract_min (node l v r) f).2, v, ?_, ?_, ?_⟩
      · cases hpair : extract_min (node l v r) f with
        | mk o t =>
            have hfst : o = some v := by
              simpa [hpair] using extract_min_fst_node l r v f
            simp [hpair, hfst]
      · exact is_min_heap_of_strongHeap (extract_min (node l v r) f).2 f
          (strongHeap_extract_min (node l v r) f
            (strongHeap_of_is_min_heap (node l v r) f hmin))
      · exact (heap_min_eq_root_of_is_min_heap l r v f hmin).symm
