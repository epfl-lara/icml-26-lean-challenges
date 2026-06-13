/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_DijkstraComposite

/- The scorer checks challenge files independently, so the heap and Dijkstra
   helper proofs are inlined here instead of imported from auxiliary files. -/

open BinaryTree BinaryHeap Finset SimpleGraph

set_option autoImplicit true

namespace BinaryTree

lemma containsb_eq_true_iff_contains {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x : α), containsb t x = true ↔ contains t x := by
  intro t x
  induction t with
  | leaf => simp [containsb, contains]
  | node l v r ihl ihr => simp [containsb, contains, ihl, ihr]

lemma contains_insert_iff {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (insert t y f) x ↔ contains t x ∨ x = y := by
  intro t x y f
  induction t generalizing y with
  | leaf =>
      simp [insert, contains]
      exact eq_comm
  | node l v r ihl ihr =>
      by_cases h : f y ≤ f v
      · simp only [insert, h, ↓reduceIte, contains, ihl]
        grind
      · simp only [insert, h, ↓reduceIte, contains, ihl]
        grind

lemma contains_merge_iff {α : Type u} :
    ∀ (t₁ t₂ : BinaryTree α) (x : α) (f : α → ENat),
      contains (merge t₁ t₂ f) x ↔ contains t₁ x ∨ contains t₂ x := by
  intro t₁ t₂ x f
  fun_induction merge t₁ t₂ f <;>
    simp only [contains, Bool.false_eq_true, false_or, or_false, *] <;> grind

lemma contains_remove_subset {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (remove t y f) x → contains t x := by
  intro t x y f
  induction t generalizing y f with
  | leaf => simp [remove, contains]
  | node l v r ihl ihr =>
      by_cases h : y = v
      · subst h
        simp only [remove, ↓reduceIte, contains_merge_iff, contains]
        intro hcase
        exact Or.inr hcase
      · simp only [remove, h, ↓reduceIte, contains]
        intro hcase
        rcases hcase with hroot | hl | hr
        · exact Or.inl hroot
        · exact Or.inr (Or.inl (ihl y f hl))
        · exact Or.inr (Or.inr (ihr y f hr))

lemma contains_remove_of_ne {α : Type u} [DecidableEq α] :
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
      · simp only [remove, h, ↓reduceIte, contains]
        rcases hmem with hvx | hl | hr
        · exact Or.inl hvx
        · exact Or.inr (Or.inl (ihl y f hl hne))
        · exact Or.inr (Or.inr (ihr y f hr hne))

lemma contains_decrease_priority_iff {α : Type u} [DecidableEq α] :
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

lemma contains_heapify_iff {α : Type u} :
    ∀ (t : BinaryTree α) (x : α) (f : α → ENat),
      contains (heapify t f) x ↔ contains t x := by
  intro t x f
  fun_induction heapify t f <;>
    simp only [contains, Bool.false_eq_true, or_self, or_false, false_or, *] <;> grind

lemma get_last_fst_isSome {α : Type u} :
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

lemma get_last_value_contains {α : Type u} :
    ∀ (t : BinaryTree α) (x : α), (get_last t).1 = some x → contains t x := by
  intro t x h
  fun_induction get_last t <;>
    simp only [reduceCtorEq, Option.some.injEq, contains, Bool.false_eq_true, or_self,
      or_false, false_or] at h ⊢ <;> grind

lemma get_last_tree_subset {α : Type u} :
    ∀ (t : BinaryTree α) (x : α), contains (get_last t).2 x → contains t x := by
  intro t x h
  fun_induction get_last t <;>
    simp only [contains, Bool.false_eq_true, false_or] at h ⊢ <;> grind

lemma get_last_value_or_tree {α : Type u} :
    ∀ (t : BinaryTree α) (x : α),
      contains t x → (get_last t).1 = some x ∨ contains (get_last t).2 x := by
  intro t x h
  fun_induction get_last t <;>
    simp only [contains, Bool.false_eq_true, or_self, or_false, Option.some.injEq,
      false_or] at h ⊢ <;> grind

lemma get_last_node_leaf_fst {α : Type u} :
    ∀ (l r : BinaryTree α) (v : α),
      (get_last (node l v r)).2 = leaf → (get_last (node l v r)).1 = some v := by
  intro l r v h
  cases l <;> cases r <;> simp [get_last] at h ⊢

lemma get_last_node_tree_root {α : Type u} :
    ∀ (l r tl tr : BinaryTree α) (v tv : α),
      (get_last (node l v r)).2 = node tl tv tr → tv = v := by
  intro l r tl tr v tv h
  cases l <;> cases r <;> simp [get_last] at h ⊢ <;> grind

lemma extract_min_fst_node {α : Type u} :
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

lemma contains_extract_min_subset {α : Type u} :
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

lemma contains_extract_min_of_ne_root {α : Type u} :
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

def StrongHeap : BinaryTree α → (α → ENat) → Prop
  | leaf, _ => True
  | node l v r, f =>
      (∀ x, contains l x → f v ≤ f x) ∧
      (∀ x, contains r x → f v ≤ f x) ∧
      StrongHeap l f ∧ StrongHeap r f

def ChildrenStrongHeap : BinaryTree α → (α → ENat) → Prop
  | leaf, _ => True
  | node l _ r, f => StrongHeap l f ∧ StrongHeap r f

lemma strongHeap_root_le {α : Type u} {l r : BinaryTree α} {v x : α} {f : α → ENat} :
    StrongHeap (node l v r) f → contains (node l v r) x → f v ≤ f x := by
  intro hheap hmem
  rcases hheap with ⟨hl, hr, hhl, hhr⟩
  rcases hmem with hvx | hx | hx
  · simp [hvx]
  · exact hl x hx
  · exact hr x hx

lemma strongHeap_insert {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      StrongHeap t f → StrongHeap (insert t y f) f := by
  intro t y f hheap
  induction t generalizing y with
  | leaf =>
      simp only [insert, StrongHeap, and_self, and_true]
      intro x hx
      cases hx
  | node l v r ihl ihr =>
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      by_cases h : f y ≤ f v
      · simp only [insert, h, ↓reduceIte, StrongHeap]
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
      · simp only [insert, h, ↓reduceIte, StrongHeap]
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

lemma strongHeap_merge {α : Type u} :
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

lemma strongHeap_heapify {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      ChildrenStrongHeap t f → StrongHeap (heapify t f) f := by
  intro t f hch
  fun_induction heapify t f with
  | case1 => simp [StrongHeap]
  | case2 v =>
      simp only [StrongHeap, and_self, and_true]
      intro x hx
      cases hx
  | case3 v rl rv rr h ih =>
      rcases hch with ⟨_, hright⟩
      rcases hright with ⟨hrl, hrr, hhrl, hhrr⟩
      simp only [StrongHeap, true_and]
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
      simp only [StrongHeap, true_and]
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
      simp only [StrongHeap, and_true]
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
      simp only [StrongHeap, and_true]
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
      simp only [StrongHeap]
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
      simp only [StrongHeap]
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
      simp only [StrongHeap]
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
      simp only [StrongHeap]
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

lemma strongHeap_get_last_tree {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      StrongHeap t f → StrongHeap (get_last t).2 f := by
  intro t f hheap
  fun_induction get_last t <;>
    simp only [StrongHeap, and_self, and_true, imp_false, true_and] at * <;>
    grind [get_last_tree_subset]

lemma strongHeap_extract_min {α : Type u} :
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

lemma strongHeap_congr {α : Type u} :
    ∀ (t : BinaryTree α) (f g : α → ENat),
      (∀ x, contains t x → f x = g x) → StrongHeap t f → StrongHeap t g := by
  intro t f g hagree hheap
  induction t with
  | leaf => simp [StrongHeap]
  | node l v r ihl ihr =>
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      simp [StrongHeap]
      constructor
      · intro x hx
        have hv : f v = g v := hagree v (Or.inl rfl)
        have hxg : f x = g x := hagree x (Or.inr (Or.inl hx))
        simpa [← hv, ← hxg] using hl x hx
      · constructor
        · intro x hx
          have hv : f v = g v := hagree v (Or.inl rfl)
          have hxg : f x = g x := hagree x (Or.inr (Or.inr hx))
          simpa [← hv, ← hxg] using hr x hx
        · constructor
          · exact ihl (fun x hx => hagree x (Or.inr (Or.inl hx))) hhl
          · exact ihr (fun x hx => hagree x (Or.inr (Or.inr hx))) hhr

lemma strongHeap_remove {α : Type u} [DecidableEq α] :
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
      · simp only [remove, hy, ↓reduceIte, StrongHeap]
        constructor
        · intro x hx
          exact hl x (contains_remove_subset l x y f hx)
        · constructor
          · intro x hx
            exact hr x (contains_remove_subset r x y f hx)
          · constructor
            · exact ihl y f hhl
            · exact ihr y f hhr

def NoDupTree : BinaryTree α → Prop
  | leaf => True
  | node l v r =>
      NoDupTree l ∧ NoDupTree r ∧ ¬ contains l v ∧ ¬ contains r v ∧
        ∀ x, contains l x → contains r x → False

lemma noDup_insert {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      NoDupTree t → ¬ contains t y → NoDupTree (insert t y f) := by
  intro t y f hnd hnot
  induction t generalizing y with
  | leaf => simp only [insert, NoDupTree, contains, Bool.false_eq_true, not_false_eq_true, imp_self, implies_true, and_self]
  | node l v r ihl ihr =>
      rcases hnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
      have hnyv : y ≠ v := by intro h; exact hnot (Or.inl h.symm)
      have hnly : ¬ contains l y := by intro h; exact hnot (Or.inr (Or.inl h))
      have hnry : ¬ contains r y := by intro h; exact hnot (Or.inr (Or.inr h))
      by_cases hle : f y ≤ f v
      · simp only [insert, hle, ↓reduceIte, NoDupTree, imp_false]
        constructor
        · exact ihl v hndl hnlv
        · constructor
          · exact hndr
          · constructor
            · intro hyin
              have hyold := (contains_insert_iff l y v f).mp hyin
              rcases hyold with hly | hyv
              · exact hnly hly
              · exact hnyv hyv
            · constructor
              · exact hnry
              · intro x hx hrx
                have hxold := (contains_insert_iff l x v f).mp hx
                rcases hxold with hxl | hxv
                · exact hdisj x hxl hrx
                · exact hnrv (by simpa [hxv] using hrx)
      · simp only [insert, hle, ↓reduceIte, NoDupTree, imp_false]
        constructor
        · exact ihl y hndl hnly
        · constructor
          · exact hndr
          · constructor
            · intro hvin
              have hvold := (contains_insert_iff l v y f).mp hvin
              rcases hvold with hlv | hvy
              · exact hnlv hlv
              · exact hnyv hvy.symm
            · constructor
              · exact hnrv
              · intro x hx hrx
                have hxold := (contains_insert_iff l x y f).mp hx
                rcases hxold with hxl | hxy
                · exact hdisj x hxl hrx
                · exact hnry (by simpa [hxy] using hrx)

lemma noDup_merge {α : Type u} :
    ∀ (t₁ t₂ : BinaryTree α) (f : α → ENat),
      NoDupTree t₁ → NoDupTree t₂ →
      (∀ x, contains t₁ x → contains t₂ x → False) →
      NoDupTree (merge t₁ t₂ f) := by
  intro t₁ t₂ f hnd₁ hnd₂ hdisj12
  fun_induction merge t₁ t₂ f with
  | case1 t => simpa [merge, NoDupTree] using hnd₂
  | case2 t => simpa [merge, NoDupTree] using hnd₁
  | case3 l1 v1 r1 l2 v2 r2 hle ih =>
      rcases hnd₁ with ⟨hndl1, hndr1, hnl1v1, hnr1v1, hdisj1⟩
      have hnd_left : NoDupTree (merge l1 (node l2 v2 r2) f) := by
        apply ih hndl1 hnd₂
        intro x hx1 hx2
        exact hdisj12 x (Or.inr (Or.inl hx1)) hx2
      simp only [NoDupTree, imp_false]
      constructor
      · exact hnd_left
      · constructor
        · exact hndr1
        · constructor
          · intro hv1left
            have hv1old := (contains_merge_iff l1 (node l2 v2 r2) v1 f).mp hv1left
            rcases hv1old with hlv | h2v
            · exact hnl1v1 hlv
            · exact hdisj12 v1 (Or.inl rfl) h2v
          · constructor
            · exact hnr1v1
            · intro x hxleft hxr1
              have hxold := (contains_merge_iff l1 (node l2 v2 r2) x f).mp hxleft
              rcases hxold with hxl1 | hx2
              · exact hdisj1 x hxl1 hxr1
              · exact hdisj12 x (Or.inr (Or.inr hxr1)) hx2
  | case4 l1 v1 r1 l2 v2 r2 hnot ih =>
      rcases hnd₂ with ⟨hndl2, hndr2, hnl2v2, hnr2v2, hdisj2⟩
      have hnd_left : NoDupTree (merge (node l1 v1 r1) l2 f) := by
        apply ih hnd₁ hndl2
        intro x hx1 hx2
        exact hdisj12 x hx1 (Or.inr (Or.inl hx2))
      simp only [NoDupTree, imp_false]
      constructor
      · exact hnd_left
      · constructor
        · exact hndr2
        · constructor
          · intro hv2left
            have hv2old := (contains_merge_iff (node l1 v1 r1) l2 v2 f).mp hv2left
            rcases hv2old with h1v | hl2v
            · exact hdisj12 v2 h1v (Or.inl rfl)
            · exact hnl2v2 hl2v
          · constructor
            · exact hnr2v2
            · intro x hxleft hxr2
              have hxold := (contains_merge_iff (node l1 v1 r1) l2 x f).mp hxleft
              rcases hxold with hx1 | hxl2
              · exact hdisj12 x hx1 (Or.inr (Or.inr hxr2))
              · exact hdisj2 x hxl2 hxr2

lemma noDup_remove {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      NoDupTree t → NoDupTree (remove t y f) := by
  intro t y f hnd
  induction t generalizing y f with
  | leaf => simp [remove, NoDupTree]
  | node l v r ihl ihr =>
      rcases hnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
      by_cases hy : y = v
      · subst hy
        simp [remove]
        exact noDup_merge l r f hndl hndr hdisj
      · simp only [remove, hy, ↓reduceIte, NoDupTree, imp_false]
        constructor
        · exact ihl y f hndl
        · constructor
          · exact ihr y f hndr
          · constructor
            · intro hvleft
              exact hnlv (contains_remove_subset l v y f hvleft)
            · constructor
              · intro hvright
                exact hnrv (contains_remove_subset r v y f hvright)
              · intro x hxleft hxright
                exact hdisj x (contains_remove_subset l x y f hxleft)
                  (contains_remove_subset r x y f hxright)

lemma remove_not_contains_of_noDup {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      NoDupTree t → ¬ contains (remove t y f) y := by
  intro t y f hnd
  induction t generalizing y f with
  | leaf => simp [remove, contains]
  | node l v r ihl ihr =>
      rcases hnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
      by_cases hy : y = v
      · subst hy
        simp [remove, contains_merge_iff]
        exact ⟨hnlv, hnrv⟩
      · simp only [remove, hy, ↓reduceIte, contains, not_or]
        constructor
        · exact fun hvy => hy hvy.symm
        · constructor
          · exact ihl y f hndl
          · exact ihr y f hndr

lemma noDup_heapify {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      NoDupTree t → NoDupTree (heapify t f) := by
  intro t f hnd
  fun_induction heapify t f <;>
    simp only [NoDupTree, contains, Bool.false_eq_true, not_false_eq_true, imp_self,
      implies_true, and_self, imp_false, and_imp, not_or, IsEmpty.forall_iff, and_true,
      true_and, not_lt, not_le] at *
  all_goals grind [contains_heapify_iff, contains]

lemma noDup_get_last_tree {α : Type u} :
    ∀ (t : BinaryTree α), NoDupTree t → NoDupTree (get_last t).2 := by
  intro t hnd
  fun_induction get_last t <;>
    simp only [NoDupTree, imp_false, imp_not_self, and_self_left, true_and] at * <;>
    grind [get_last_tree_subset]

lemma get_last_value_not_in_tree {α : Type u} :
    ∀ (t : BinaryTree α) (x : α),
      NoDupTree t → (get_last t).1 = some x → ¬ contains (get_last t).2 x := by
  intro t x hnd hval hmem
  fun_induction get_last t <;>
    simp only [NoDupTree, reduceCtorEq, contains, Bool.false_eq_true, not_false_eq_true,
      imp_self, implies_true, and_self, Option.some.injEq, imp_false, IsEmpty.forall_iff,
      and_true, true_and, false_or] at * <;>
    grind [get_last_value_contains, get_last_tree_subset]

lemma noDup_extract_min {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      NoDupTree t → NoDupTree (extract_min t f).2 := by
  intro t f hnd
  unfold extract_min
  cases hlast : get_last t with
  | mk o rest =>
      cases o with
      | none => simp [NoDupTree]
      | some last =>
          cases hrest : rest with
          | leaf => simp [NoDupTree]
          | node l v r =>
              have hrestnd : NoDupTree (node l v r) := by
                have := noDup_get_last_tree t hnd
                simpa [hlast, hrest] using this
              have hlast_not : ¬ contains (node l v r) last := by
                have := get_last_value_not_in_tree t last hnd
                  (by simpa [hlast] using congrArg Prod.fst hlast)
                simpa [hlast, hrest] using this
              rcases hrestnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
              simp [hrest]
              apply noDup_heapify
              simp [NoDupTree]
              constructor
              · exact hndl
              · constructor
                · exact hndr
                · constructor
                  · intro hl
                    exact hlast_not (Or.inr (Or.inl hl))
                  · constructor
                    · intro hr
                      exact hlast_not (Or.inr (Or.inr hr))
                    · exact hdisj

lemma strongHeap_remove_changed {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (old new : α → ENat),
      NoDupTree t → StrongHeap t old →
      (∀ x, x ≠ y → new x = old x) →
      StrongHeap (remove t y new) new := by
  intro t y old new hnd hheap hagree
  induction t generalizing y old new with
  | leaf => simp [remove, StrongHeap]
  | node l v r ihl ihr =>
      rcases hnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      by_cases hy : y = v
      · subst hy
        simp [remove]
        have hlnew : StrongHeap l new := by
          apply strongHeap_congr l old new
          · intro x hx
            exact (hagree x (by intro hxv; exact hnlv (by simpa [hxv] using hx))).symm
          · exact hhl
        have hrnew : StrongHeap r new := by
          apply strongHeap_congr r old new
          · intro x hx
            exact (hagree x (by intro hxv; exact hnrv (by simpa [hxv] using hx))).symm
          · exact hhr
        exact strongHeap_merge l r new hlnew hrnew
      · have hvagree : new v = old v := hagree v (by intro h; exact hy h.symm)
        simp only [remove, hy, ↓reduceIte, StrongHeap]
        constructor
        · intro x hx
          have hxoldmem := contains_remove_subset l x y new hx
          have hxney : x ≠ y := by
            intro hxy
            have hbad := remove_not_contains_of_noDup l y new hndl
            exact hbad (by simpa [hxy] using hx)
          have hxagree : new x = old x := hagree x hxney
          simpa [hvagree, hxagree] using hl x hxoldmem
        · constructor
          · intro x hx
            have hxoldmem := contains_remove_subset r x y new hx
            have hxney : x ≠ y := by
              intro hxy
              have hbad := remove_not_contains_of_noDup r y new hndr
              exact hbad (by simpa [hxy] using hx)
            have hxagree : new x = old x := hagree x hxney
            simpa [hvagree, hxagree] using hr x hxoldmem
          · constructor
            · exact ihl y old new hndl hhl hagree
            · exact ihr y old new hndr hhr hagree

lemma strongHeap_decrease_priority_changed {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (old new : α → ENat),
      NoDupTree t → StrongHeap t old →
      (∀ x, x ≠ y → new x = old x) →
      StrongHeap (decrease_priority t y new) new := by
  intro t y old new hnd hheap hagree
  by_cases hy : containsb t y = true
  · have hrem := strongHeap_remove_changed t y old new hnd hheap hagree
    simp [decrease_priority, hy]
    exact strongHeap_insert (remove t y new) y new hrem
  · have hnot : ¬ contains t y := by
      intro hmem
      exact hy ((containsb_eq_true_iff_contains t y).mpr hmem)
    simp [decrease_priority, hy]
    apply strongHeap_congr t old new
    · intro x hx
      exact (hagree x (by intro hxy; exact hnot (by simpa [hxy] using hx))).symm
    · exact hheap

lemma noDup_decrease_priority {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      NoDupTree t → NoDupTree (decrease_priority t y f) := by
  intro t y f hnd
  by_cases hy : containsb t y = true
  · simp [decrease_priority, hy]
    apply noDup_insert
    · exact noDup_remove t y f hnd
    · exact remove_not_contains_of_noDup t y f hnd
  · simp [decrease_priority, hy]
    exact hnd

end BinaryTree

namespace BinaryHeap

def Mem {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x : α) : Prop :=
  BinaryTree.contains q.tree x

def Strong {α : Type u} [DecidableEq α] (q : BinaryHeap α) (f : α → ENat) : Prop :=
  BinaryTree.StrongHeap q.tree f

def NoDup {α : Type u} [DecidableEq α] (q : BinaryHeap α) : Prop :=
  BinaryTree.NoDupTree q.tree

lemma not_mem_of_isEmpty {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x : α) :
    q.isEmpty = true → ¬ Mem q x := by
  rcases q with ⟨t⟩
  cases t <;> simp [BinaryHeap.isEmpty, Mem, BinaryTree.contains]

lemma mem_add_iff {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x y : α)
    (f : α → ENat) :
    Mem (q.add y f) x ↔ Mem q x ∨ x = y := by
  rcases q with ⟨t⟩
  simpa [Mem, BinaryHeap.add] using BinaryTree.contains_insert_iff t x y f

lemma mem_decrease_priority_iff {α : Type u} [DecidableEq α] (q : BinaryHeap α)
    (x y : α) (f : α → ENat) :
    Mem (q.decrease_priority y f) x ↔ Mem q x := by
  rcases q with ⟨t⟩
  simpa [Mem, BinaryHeap.decrease_priority] using
    BinaryTree.contains_decrease_priority_iff t x y f

lemma mem_extract_min_subset {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) (x : α) :
    Mem (q.extract_min f hne).2 x → Mem q x := by
  rcases q with ⟨t⟩
  simpa [Mem, BinaryHeap.extract_min] using BinaryTree.contains_extract_min_subset t x f

lemma mem_extract_min_of_ne_fst {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) (x : α) :
    Mem q x → x ≠ (q.extract_min f hne).1 → Mem (q.extract_min f hne).2 x := by
  rcases q with ⟨t⟩
  cases t with
  | leaf =>
      simp [Mem, BinaryTree.contains]
  | node l root r =>
      intro hx hxne
      have hfst :
          (BinaryHeap.extract_min ({ tree := node l root r } : BinaryHeap α) f hne).1 = root :=
        by simp [BinaryHeap.extract_min, BinaryTree.extract_min_fst_node]
      have hxne_root : x ≠ root := by
        intro hxr
        exact hxne (by simpa [hfst, hxr])
      simpa [Mem, BinaryHeap.extract_min] using
        BinaryTree.contains_extract_min_of_ne_root l r root x f hx hxne_root

lemma mem_extract_min_cases {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) (x : α) :
    Mem q x → x = (q.extract_min f hne).1 ∨ Mem (q.extract_min f hne).2 x := by
  intro hx
  by_cases hxf : x = (q.extract_min f hne).1
  · exact Or.inl hxf
  · exact Or.inr (mem_extract_min_of_ne_fst q f hne x hx hxf)

lemma strong_add {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x : α)
    (f : α → ENat) :
    Strong q f → Strong (q.add x f) f := by
  rcases q with ⟨t⟩
  exact BinaryTree.strongHeap_insert t x f

lemma noDup_add {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x : α)
    (f : α → ENat) :
    NoDup q → ¬ Mem q x → NoDup (q.add x f) := by
  rcases q with ⟨t⟩
  exact BinaryTree.noDup_insert t x f

lemma strong_extract_min {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) :
    Strong q f → Strong (q.extract_min f hne).2 f := by
  rcases q with ⟨t⟩
  simpa [Strong, BinaryHeap.extract_min] using BinaryTree.strongHeap_extract_min t f

lemma noDup_extract_min {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) :
    NoDup q → NoDup (q.extract_min f hne).2 := by
  rcases q with ⟨t⟩
  simpa [NoDup, BinaryHeap.extract_min] using BinaryTree.noDup_extract_min t f

lemma strong_decrease_priority_changed {α : Type u} [DecidableEq α]
    (q : BinaryHeap α) (y : α) (old new : α → ENat) :
    NoDup q → Strong q old → (∀ x, x ≠ y → new x = old x) →
    Strong (q.decrease_priority y new) new := by
  rcases q with ⟨t⟩
  exact BinaryTree.strongHeap_decrease_priority_changed t y old new

lemma noDup_decrease_priority {α : Type u} [DecidableEq α]
    (q : BinaryHeap α) (y : α) (f : α → ENat) :
    NoDup q → NoDup (q.decrease_priority y f) := by
  rcases q with ⟨t⟩
  exact BinaryTree.noDup_decrease_priority t y f

lemma extract_min_fst_node_heap {α : Type u} [DecidableEq α] [Nonempty α]
    (l r : BinaryTree α) (u : α) (f : α → ENat)
    (hne : ¬(BinaryHeap.isEmpty ({ tree := node l u r } : BinaryHeap α)) = true) :
    (BinaryHeap.extract_min ({ tree := node l u r } : BinaryHeap α) f hne).1 = u := by
  simp [BinaryHeap.extract_min, BinaryTree.extract_min_fst_node]

end BinaryHeap

open BinaryTree BinaryHeap Finset SimpleGraph

set_option autoImplicit true

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

lemma walk_boundary {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (P : V → Prop) [DecidablePred P]
    (ha : ¬ P a) (hb : P b) :
    ∃ x y, ∃ q : G.Walk a x, ¬ P x ∧ P y ∧ G.Adj x y ∧ q.length + 1 ≤ p.length := by
  induction p with
  | nil => exact False.elim (ha hb)
  | cons h p ih =>
      case _ u v w =>
      by_cases hp : P v
      · refine ⟨_, _, Walk.nil, ha, hp, h, ?_⟩
        simp [Walk.length_cons]
      · rcases ih hp hb with ⟨x, y, q, hx, hy, hxy, hlen⟩
        refine ⟨x, y, Walk.cons h q, hx, hy, hxy, ?_⟩
        simp [Walk.length_cons]
        omega

end SimpleGraph

lemma delta_adj_le [Nonempty V] (g : fin_simple_graph V) (s u v : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) (hadj : g.Adj u v) :
    delta g s v ≤ delta g s u + 1 := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist s u
  have hle := SimpleGraph.dist_le (p.concat hadj)
  rw [SimpleGraph.Walk.length_concat, hp] at hle
  simpa [delta] using hle

lemma relax_neighbors_mem_iff (g : fin_simple_graph V) (u x : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    BinaryHeap.Mem (relax_neighbors g u dist q).2 x ↔ BinaryHeap.Mem q x := by
  unfold relax_neighbors
  generalize hs : (g.neighborFinset u).val.toList = xs
  clear hs
  induction xs generalizing dist q with
  | nil => simp
  | cons v xs ih =>
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hih := ih dist' (q.decrease_priority v dist')
        simpa [List.foldl, hlt, dist'] using
          (hih.trans (BinaryHeap.mem_decrease_priority_iff q x v dist'))
      · have hih := ih dist q
        simpa [List.foldl, hlt] using hih

lemma relax_neighbors_good (g : fin_simple_graph V) (u : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    BinaryHeap.NoDup q → BinaryHeap.Strong q dist →
    BinaryHeap.NoDup (relax_neighbors g u dist q).2 ∧
      BinaryHeap.Strong (relax_neighbors g u dist q).2 (relax_neighbors g u dist q).1 := by
  unfold relax_neighbors
  generalize hs : (g.neighborFinset u).val.toList = xs
  clear hs
  induction xs generalizing dist q with
  | nil =>
      intro hnd hstrong
      simp [hnd, hstrong]
  | cons v xs ih =>
      intro hnd hstrong
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hagree : ∀ x, x ≠ v → dist' x = dist x := by intro x hx; simp [dist', hx]
        have hstrong' : BinaryHeap.Strong (q.decrease_priority v dist') dist' :=
          BinaryHeap.strong_decrease_priority_changed q v dist dist' hnd hstrong hagree
        have hnd' : BinaryHeap.NoDup (q.decrease_priority v dist') :=
          BinaryHeap.noDup_decrease_priority q v dist' hnd
        have hih := ih dist' (q.decrease_priority v dist') hnd' hstrong'
        simpa [List.foldl, hlt, dist'] using hih
      · have hih := ih dist q hnd hstrong
        simpa [List.foldl, hlt] using hih

lemma relax_list_dist_le (xs : List V) (u x : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    (List.foldl
      (fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
        let (dist, queue) := acc
        let alt := dist u + 1
        if alt < dist v then
          let dist' : V → ENat := fun x => if x = v then alt else dist x
          let queue' := queue.decrease_priority v dist'
          (dist', queue')
        else
          (dist, queue))
      (dist, q) xs).1 x ≤ dist x := by
  induction xs generalizing dist q with
  | nil => simp
  | cons v xs ih =>
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hstep : dist' x ≤ dist x := by
          by_cases hx : x = v
          · subst x
            simp [dist']
            exact le_of_lt hlt
          · simp [dist', hx]
        have hih := ih dist' (q.decrease_priority v dist')
        exact le_trans (by simpa [List.foldl, hlt, dist'] using hih) hstep
      · have hih := ih dist q
        simpa [List.foldl, hlt] using hih

lemma relax_neighbors_dist_le (g : fin_simple_graph V) (u x : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    (relax_neighbors g u dist q).1 x ≤ dist x := by
  unfold relax_neighbors
  exact relax_list_dist_le (g.neighborFinset u).val.toList u x dist q

lemma relax_neighbors_source_zero (g : fin_simple_graph V) (u s : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    dist s = 0 → (relax_neighbors g u dist q).1 s = 0 := by
  intro hs0
  unfold relax_neighbors
  generalize hslist : (g.neighborFinset u).val.toList = xs
  clear hslist
  induction xs generalizing dist q with
  | nil => simpa using hs0
  | cons v xs ih =>
      by_cases hlt : dist u + 1 < dist v
      · by_cases hsv : s = v
        · subst hsv
          have : ¬ dist u + 1 < 0 := not_lt_of_ge bot_le
          exact False.elim (this (by simpa [hs0] using hlt))
        · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
          have hs0' : dist' s = 0 := by simp [dist', hsv, hs0]
          simpa [List.foldl, hlt, dist'] using ih dist' (q.decrease_priority v dist') hs0'
      · simpa [List.foldl, hlt] using ih dist q hs0

lemma relax_neighbors_lower [Nonempty V] (g : fin_simple_graph V) (u s : V)
    (dist : V → ENat) (q : BinaryHeap V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph)
    (hu : dist u = (delta g s u : ENat))
    (hlower : ∀ x, (delta g s x : ENat) ≤ dist x) :
    ∀ x, (delta g s x : ENat) ≤ (relax_neighbors g u dist q).1 x := by
  unfold relax_neighbors
  generalize hslist : (g.neighborFinset u).val.toList = xs
  have hadjall : ∀ v, v ∈ xs → g.Adj u v := by
    intro v hv
    rw [← hslist] at hv
    simpa using hv
  clear hslist
  induction xs generalizing dist q with
  | nil => simpa using hlower
  | cons v xs ih =>
      have hadjv : g.Adj u v := hadjall v (by simp)
      have huv : u ≠ v := hadjv.ne
      have hadjtail : ∀ w, w ∈ xs → g.Adj u w := by
        intro w hw
        exact hadjall w (by simp [hw])
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hlower' : ∀ x, (delta g s x : ENat) ≤ dist' x := by
          intro x
          by_cases hx : x = v
          · have hnat := delta_adj_le g s u v hconn hadjv
            subst x
            have hcast : (delta g s v : ENat) ≤ (delta g s u : ENat) + 1 := by
              exact_mod_cast hnat
            simpa [dist', hu] using hcast
          · simp [dist', hx, hlower x]
        have hu' : dist' u = (delta g s u : ENat) := by
          simp [dist', huv, hu]
        have hih := ih dist' (q.decrease_priority v dist') hu' hlower' hadjtail
        simpa [List.foldl, hlt, dist'] using hih
      · have hih := ih dist q hu hlower hadjtail
        simpa [List.foldl, hlt] using hih

lemma relax_neighbors_neighbor_bound (g : fin_simple_graph V) (u y : V)
    (dist : V → ENat) (q : BinaryHeap V) (hadjuy : g.Adj u y) :
    (relax_neighbors g u dist q).1 y ≤ dist u + 1 := by
  unfold relax_neighbors
  generalize hslist : (g.neighborFinset u).val.toList = xs
  have hadjall : ∀ v, v ∈ xs → g.Adj u v := by
    intro v hv
    rw [← hslist] at hv
    simpa using hv
  have hy_mem : y ∈ xs := by
    rw [← hslist]
    simpa using hadjuy
  clear hslist
  induction xs generalizing dist q with
  | nil => simp at hy_mem
  | cons v xs ih =>
      have hadjv : g.Adj u v := hadjall v (by simp)
      have huv : u ≠ v := hadjv.ne
      have hadjtail : ∀ w, w ∈ xs → g.Adj u w := by
        intro w hw
        exact hadjall w (by simp [hw])
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hdu : dist' u = dist u := by simp [dist', huv]
        by_cases hyv : y = v
        · subst y
          have htail := relax_list_dist_le xs u v dist' (q.decrease_priority v dist')
          have hstep : dist' v ≤ dist u + 1 := by simp [dist']
          exact le_trans (by simpa [relax_neighbors, List.foldl, hlt, dist'] using htail) hstep
        · have hymem_tail : y ∈ xs := by
            simp at hy_mem
            exact hy_mem.resolve_left (fun h => hyv h)
          have hih := ih dist' (q.decrease_priority v dist') hadjtail hymem_tail
          simpa [List.foldl, hlt, dist', hdu] using hih
      · by_cases hyv : y = v
        · subst y
          have htail := relax_list_dist_le xs u v dist q
          have hstep : dist v ≤ dist u + 1 := le_of_not_gt hlt
          exact le_trans (by simpa [relax_neighbors, List.foldl, hlt] using htail) hstep
        · have hymem_tail : y ∈ xs := by
            simp at hy_mem
            exact hy_mem.resolve_left (fun h => hyv h)
          have hih := ih dist q hadjtail hymem_tail
          simpa [List.foldl, hlt] using hih

lemma relax_neighbors_eq_of_not_improve (g : fin_simple_graph V) (u x : V)
    (dist : V → ENat) (q : BinaryHeap V)
    (hnot : g.Adj u x → ¬ dist u + 1 < dist x) :
    (relax_neighbors g u dist q).1 x = dist x := by
  unfold relax_neighbors
  generalize hslist : (g.neighborFinset u).val.toList = xs
  have hadjall : ∀ v, v ∈ xs → g.Adj u v := by
    intro v hv
    rw [← hslist] at hv
    simpa using hv
  clear hslist
  induction xs generalizing dist q with
  | nil => simp
  | cons v xs ih =>
      have hadjv : g.Adj u v := hadjall v (by simp)
      have huv : u ≠ v := hadjv.ne
      have hadjtail : ∀ w, w ∈ xs → g.Adj u w := by
        intro w hw
        exact hadjall w (by simp [hw])
      by_cases hlt : dist u + 1 < dist v
      · have hvx : v ≠ x := by
          intro hvx
          exact hnot (by simpa [hvx] using hadjv) (by simpa [hvx] using hlt)
        let dist' : V → ENat := fun z => if z = v then dist u + 1 else dist z
        have hdu : dist' u = dist u := by simp [dist', huv]
        have hxv : x ≠ v := by intro hxv; exact hvx hxv.symm
        have hdx : dist' x = dist x := by simp [dist', hxv]
        have hnot' : g.Adj u x → ¬ dist' u + 1 < dist' x := by
          intro hux
          simpa [hdu, hdx] using hnot hux
        have hih := ih dist' (q.decrease_priority v dist') hnot' hadjtail
        simpa [List.foldl, hlt, dist', hdx] using hih
      · have hih := ih dist q hnot hadjtail
        simpa [List.foldl, hlt] using hih

lemma relax_neighbors_settled_eq [Nonempty V] (g : fin_simple_graph V) (s u x : V)
    (dist : V → ENat) (q : BinaryHeap V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph)
    (hu : dist u = (delta g s u : ENat))
    (hx : dist x = (delta g s x : ENat)) :
    (relax_neighbors g u dist q).1 x = dist x := by
  apply relax_neighbors_eq_of_not_improve
  intro hux hlt
  have hnat := delta_adj_le g s u x hconn hux
  have hδ : (delta g s x : ENat) ≤ (delta g s u : ENat) + 1 := by
    exact_mod_cast hnat
  have hle : dist x ≤ dist u + 1 := by
    simpa [hu, hx] using hδ
  exact (not_lt_of_ge hle) hlt

def DijkstraInv [Nonempty V] (g : fin_simple_graph V) (s : V)
    (dist : V → ENat) (q : BinaryHeap V) : Prop :=
  BinaryHeap.NoDup q ∧ BinaryHeap.Strong q dist ∧ dist s = 0 ∧
  (∀ x, (delta g s x : ENat) ≤ dist x) ∧
  (∀ x, ¬ BinaryHeap.Mem q x → dist x = (delta g s x : ENat)) ∧
  (∀ x y, ¬ BinaryHeap.Mem q x → BinaryHeap.Mem q y → g.Adj x y →
    dist y ≤ (delta g s x : ENat) + 1)

lemma extracted_correct [Nonempty V] (g : fin_simple_graph V) (s : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) (dist : V → ENat)
    (q : BinaryHeap V) (hne : ¬q.isEmpty = true)
    (hinv : DijkstraInv g s dist q) :
    dist (q.extract_min dist hne).1 = (delta g s (q.extract_min dist hne).1 : ENat) := by
  rcases q with ⟨t⟩
  cases t with
  | leaf => simp [BinaryHeap.isEmpty] at hne
  | node l u r =>
      classical
      have hu_extract :
          (BinaryHeap.extract_min ({ tree := node l u r } : BinaryHeap V) dist hne).1 = u :=
        BinaryHeap.extract_min_fst_node_heap l r u dist hne
      rw [hu_extract]
      rcases hinv with ⟨hnd, hstrong, hs0, hlower, hsettled, hfrontier⟩
      by_cases hus : u = s
      · have hdu0 : dist u = 0 := by simpa [hus] using hs0
        have hδu : delta g s u = 0 := by
          simp [delta, hus, SimpleGraph.dist_self]
        simpa [hδu] using hdu0
      · have hu_mem : BinaryHeap.Mem ({ tree := node l u r } : BinaryHeap V) u := by
          simp [BinaryHeap.Mem, BinaryTree.contains]
        have hs_not_mem : ¬ BinaryHeap.Mem ({ tree := node l u r } : BinaryHeap V) s := by
          intro hs_mem
          have hmin : dist u ≤ dist s := BinaryTree.strongHeap_root_le hstrong hs_mem
          have hdu0 : dist u = 0 := le_antisymm (by simpa [hs0] using hmin) bot_le
          have hδu0_enat : (delta g s u : ENat) = 0 :=
            le_antisymm (by simpa [hdu0] using hlower u) bot_le
          have hδu0 : delta g s u = 0 := by exact_mod_cast hδu0_enat
          have hzeroiff := (hconn.dist_eq_zero_iff (u := s) (v := u))
          have hs_eq_u : s = u := by
            exact hzeroiff.mp (by simpa [delta] using hδu0)
          exact hus hs_eq_u.symm
        obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist s u
        rcases SimpleGraph.walk_boundary p
            (fun x => BinaryHeap.Mem ({ tree := node l u r } : BinaryHeap V) x)
            hs_not_mem hu_mem with
          ⟨x, y, qwalk, hx_not, hy_mem, hxy, hlen⟩
        have hfront := hfrontier x y hx_not hy_mem hxy
        have hminy : dist u ≤ dist y := BinaryTree.strongHeap_root_le hstrong hy_mem
        have hdistx_nat : delta g s x ≤ qwalk.length := by
          simpa [delta] using SimpleGraph.dist_le qwalk
        have hboundary_nat : delta g s x + 1 ≤ delta g s u := by
          have hpδ : p.length = delta g s u := by
            simpa [delta] using hp
          rw [← hpδ]
          omega
        have hboundary_enat : (delta g s x : ENat) + 1 ≤ (delta g s u : ENat) := by
          exact_mod_cast hboundary_nat
        have hdu_le_delta : dist u ≤ (delta g s u : ENat) :=
          le_trans hminy (le_trans hfront hboundary_enat)
        exact le_antisymm hdu_le_delta (hlower u)

lemma dijkstra_step_inv [Nonempty V] (g : fin_simple_graph V) (s : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) (dist : V → ENat)
    (q : BinaryHeap V) (hne : ¬q.isEmpty = true)
    (hinv : DijkstraInv g s dist q) :
    DijkstraInv g s
      (relax_neighbors g (q.extract_min dist hne).1 dist (q.extract_min dist hne).2).1
      (relax_neighbors g (q.extract_min dist hne).1 dist (q.extract_min dist hne).2).2 := by
  let u := (q.extract_min dist hne).1
  let q' := (q.extract_min dist hne).2
  let relaxed := relax_neighbors g u dist q'
  rcases hinv with ⟨hnd, hstrong, hs0, hlower, hsettled, hfrontier⟩
  have hu : dist u = (delta g s u : ENat) := by
    simpa [u] using extracted_correct g s hconn dist q hne
      ⟨hnd, hstrong, hs0, hlower, hsettled, hfrontier⟩
  have hnd_extract : BinaryHeap.NoDup q' :=
    BinaryHeap.noDup_extract_min q dist hne hnd
  have hstrong_extract : BinaryHeap.Strong q' dist :=
    BinaryHeap.strong_extract_min q dist hne hstrong
  have hgood := relax_neighbors_good g u dist q' hnd_extract hstrong_extract
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [relaxed, u, q'] using hgood.1
  · simpa [relaxed, u, q'] using hgood.2
  · simpa [relaxed, u, q'] using
      relax_neighbors_source_zero g u s dist q' hs0
  · intro x
    simpa [relaxed, u, q'] using
      relax_neighbors_lower g u s dist q' hconn hu hlower x
  · intro x hx_not_new
    have hx_not_q' : ¬ BinaryHeap.Mem q' x := by
      intro hxq'
      exact hx_not_new ((relax_neighbors_mem_iff g u x dist q').2 hxq')
    by_cases hxq : BinaryHeap.Mem q x
    · rcases BinaryHeap.mem_extract_min_cases q dist hne x hxq with hxu | hxq'
      · subst hxu
        have hpres := relax_neighbors_settled_eq g s u u dist q' hconn hu hu
        calc
          relaxed.1 u = dist u := by simpa [relaxed, u, q'] using hpres
          _ = (delta g s u : ENat) := hu
      · exact False.elim (hx_not_q' hxq')
    · have hxexact := hsettled x hxq
      have hpres := relax_neighbors_settled_eq g s u x dist q' hconn hu hxexact
      calc
        relaxed.1 x = dist x := by simpa [relaxed, u, q'] using hpres
        _ = (delta g s x : ENat) := hxexact
  · intro x y hx_not_new hy_new hxy
    have hx_not_q' : ¬ BinaryHeap.Mem q' x := by
      intro hxq'
      exact hx_not_new ((relax_neighbors_mem_iff g u x dist q').2 hxq')
    have hy_q' : BinaryHeap.Mem q' y := by
      exact (relax_neighbors_mem_iff g u y dist q').1 hy_new
    have hy_q : BinaryHeap.Mem q y :=
      BinaryHeap.mem_extract_min_subset q dist hne y hy_q'
    by_cases hxq : BinaryHeap.Mem q x
    · rcases BinaryHeap.mem_extract_min_cases q dist hne x hxq with hxu | hxq'
      · subst hxu
        have hbound := relax_neighbors_neighbor_bound g u y dist q' hxy
        simpa [relaxed, u, q', hu] using hbound
      · exact False.elim (hx_not_q' hxq')
    · exact le_trans (by
        simpa [relaxed, u, q'] using relax_neighbors_dist_le g u y dist q')
        (hfrontier x y hxq hy_q hxy)

lemma dijkstra_rec_correct_of_inv [Nonempty V] (g : fin_simple_graph V) (s target : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) (dist : V → ENat)
    (q : BinaryHeap V) :
    DijkstraInv g s dist q →
      ∀ v : V, dijkstra_rec g s target dist q v = (delta g s v : ENat) := by
  refine dijkstra_rec.induct (g := g)
    (motive := fun dist q =>
      DijkstraInv g s dist q →
        ∀ v : V, dijkstra_rec g s target dist q v = (delta g s v : ENat))
    ?base ?step dist q
  · intro dist q hq hinv v
    rw [dijkstra_rec.eq_def]
    simp [hq]
    rcases hinv with ⟨_, _, _, _, hsettled, _⟩
    exact hsettled v (BinaryHeap.not_mem_of_isEmpty q v hq)
  · intro dist q hq hne
    dsimp
    intro ih hinv v
    rw [dijkstra_rec.eq_def]
    simp [hq]
    exact ih (dijkstra_step_inv g s hconn dist q hne hinv) v

lemma fold_add_mem_iff (xs : List V) (dist : V → ENat) (q : BinaryHeap V)
    (x : V) :
    BinaryHeap.Mem (xs.foldl (fun acc v => acc.add v dist) q) x ↔
      BinaryHeap.Mem q x ∨ x ∈ xs := by
  induction xs generalizing q with
  | nil => simp
  | cons v xs ih =>
      rw [List.foldl_cons]
      simp only [ih, BinaryHeap.mem_add_iff, List.mem_cons]
      grind

lemma fold_add_strong (xs : List V) (dist : V → ENat) (q : BinaryHeap V) :
    BinaryHeap.Strong q dist →
      BinaryHeap.Strong (xs.foldl (fun acc v => acc.add v dist) q) dist := by
  induction xs generalizing q with
  | nil => simpa
  | cons v xs ih =>
      intro hstrong
      rw [List.foldl_cons]
      exact ih (q.add v dist) (BinaryHeap.strong_add q v dist hstrong)

lemma fold_add_noDup (xs : List V) (dist : V → ENat) (q : BinaryHeap V) :
    xs.Nodup → (∀ x, x ∈ xs → ¬ BinaryHeap.Mem q x) → BinaryHeap.NoDup q →
      BinaryHeap.NoDup (xs.foldl (fun acc v => acc.add v dist) q) := by
  induction xs generalizing q with
  | nil =>
      intro _ _ hnd
      simpa
  | cons v xs ih =>
      intro hnodup hfresh hnd
      rcases List.nodup_cons.mp hnodup with ⟨hv_not_xs, hxs_nodup⟩
      have hv_fresh : ¬ BinaryHeap.Mem q v := hfresh v (by simp)
      have hnd_add : BinaryHeap.NoDup (q.add v dist) :=
        BinaryHeap.noDup_add q v dist hnd hv_fresh
      have hfresh_tail : ∀ x, x ∈ xs → ¬ BinaryHeap.Mem (q.add v dist) x := by
        intro x hx hmem
        have hmem' := (BinaryHeap.mem_add_iff q x v dist).mp hmem
        rcases hmem' with hxq | hxv
        · exact hfresh x (by simp [hx]) hxq
        · exact hv_not_xs (by simpa [hxv] using hx)
      rw [List.foldl_cons]
      exact ih (q.add v dist) hxs_nodup hfresh_tail hnd_add

lemma initial_dijkstra_inv [Nonempty V] (g : fin_simple_graph V) (s : V) :
    let dist : V → ENat := fun v => if v = s then 0 else ⊤
    let q := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist) BinaryHeap.empty
    DijkstraInv g s dist q := by
  intro dist q
  have hmem_all : ∀ x : V, BinaryHeap.Mem q x := by
    intro x
    have hxlist : x ∈ (Finset.univ : Finset V).val.toList := by
      simpa using (Finset.mem_univ x)
    have hx := (fold_add_mem_iff (Finset.univ : Finset V).val.toList dist
      BinaryHeap.empty x).2 (Or.inr hxlist)
    simpa [q] using hx
  have hstrong_empty : BinaryHeap.Strong (BinaryHeap.empty : BinaryHeap V) dist := by
    simp [BinaryHeap.Strong, BinaryHeap.empty, BinaryTree.StrongHeap]
  have hstrong : BinaryHeap.Strong q dist := by
    simpa [q] using
      fold_add_strong (Finset.univ : Finset V).val.toList dist
        (BinaryHeap.empty : BinaryHeap V) hstrong_empty
  have hnodup_list : ((Finset.univ : Finset V).val.toList).Nodup := by
    simpa using Finset.nodup_toList (Finset.univ : Finset V)
  have hfresh_empty :
      ∀ x, x ∈ (Finset.univ : Finset V).val.toList →
        ¬ BinaryHeap.Mem (BinaryHeap.empty : BinaryHeap V) x := by
    intro x _ hx
    simpa [BinaryHeap.Mem, BinaryHeap.empty, BinaryTree.contains] using hx
  have hnd_empty : BinaryHeap.NoDup (BinaryHeap.empty : BinaryHeap V) := by
    simp [BinaryHeap.NoDup, BinaryHeap.empty, BinaryTree.NoDupTree]
  have hnd : BinaryHeap.NoDup q := by
    simpa [q] using
      fold_add_noDup (Finset.univ : Finset V).val.toList dist
        (BinaryHeap.empty : BinaryHeap V) hnodup_list hfresh_empty hnd_empty
  refine ⟨hnd, hstrong, ?_, ?_, ?_, ?_⟩
  · simp [dist]
  · intro x
    by_cases hxs : x = s
    · subst hxs
      simp [dist, delta, SimpleGraph.dist_self]
    · simp [dist, hxs]
  · intro x hx_not
    exact False.elim (hx_not (hmem_all x))
  · intro x y hx_not _ _
    exact False.elim (hx_not (hmem_all x))

theorem dijkstra_correctness_aux [Nonempty V] (g : fin_simple_graph V) (s target : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) :
    ∀ v : V, (dijkstra g s target) v = (delta g s v : ENat) := by
  let dist : V → ENat := fun v => if v = s then 0 else ⊤
  let q := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist) BinaryHeap.empty
  have hinv : DijkstraInv g s dist q := by
    simpa [dist, q] using initial_dijkstra_inv g s
  intro v
  simpa [dijkstra, dist, q] using
    dijkstra_rec_correct_of_inv g s target hconn dist q hinv v

/-
  Main correctness theorem: for every vertex `v`, Dijkstra computes the true shortest-path length
  from `s` to `v`. That is, `(dijkstra g s v) v = delta g s v` when the graph is connected.
-/
theorem dijkstra_correctness
  [Nonempty V]
  (g : fin_simple_graph V) (s : V)
  (is_connected : SimpleGraph.Connected g.toSimpleGraph) :
  ∀ v : V, (dijkstra g s v) v = delta g s v := by
  intro v
  simpa using dijkstra_correctness_aux g s v is_connected v
