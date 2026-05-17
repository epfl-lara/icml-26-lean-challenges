/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Challenge_BinaryHeap_1

open BinaryTree

-- extract_min_correctness:
-- correctness for `extract_min`:
-- - The members remain the same except for the extracted minimum.
-- - If the input was a min-heap, extracting returns some value `v'` and a
--   resulting tree that is a min-heap; furthermore the extracted priority
--   equals `heap_min bt f`.
-- The proof composes containment lemmas, `get_last` properties and
-- `heapify` correctness used in `extract_min_correct_node`.
private def rootLe {α : Type u} (f : α → ENat) (p : ENat) : BinaryTree α → Prop
  | leaf => True
  | node _ v _ => p ≤ f v

private theorem min_heap_left_of_node {α : Type u} (f : α → ENat) :
    ∀ (l : BinaryTree α) (v : α) (r : BinaryTree α),
      is_min_heap (node l v r) f → is_min_heap l f := by
  intro l v r h
  cases l <;> cases r <;> simp [is_min_heap] at h ⊢
  all_goals tauto

private theorem min_heap_right_of_node {α : Type u} (f : α → ENat) :
    ∀ (l : BinaryTree α) (v : α) (r : BinaryTree α),
      is_min_heap (node l v r) f → is_min_heap r f := by
  intro l v r h
  cases l <;> cases r <;> simp [is_min_heap] at h ⊢
  all_goals tauto

private theorem rootLe_left_of_node {α : Type u} (f : α → ENat) :
    ∀ (l : BinaryTree α) (v : α) (r : BinaryTree α),
      is_min_heap (node l v r) f → rootLe f (f v) l := by
  intro l v r h
  cases l <;> cases r <;> simp [rootLe, is_min_heap] at h ⊢
  all_goals tauto

private theorem rootLe_right_of_node {α : Type u} (f : α → ENat) :
    ∀ (l : BinaryTree α) (v : α) (r : BinaryTree α),
      is_min_heap (node l v r) f → rootLe f (f v) r := by
  intro l v r h
  cases l <;> cases r <;> simp [rootLe, is_min_heap] at h ⊢
  all_goals tauto

private theorem rootLe_get_last_snd {α : Type u} (f : α → ENat) (p : ENat) :
    ∀ (bt : BinaryTree α), rootLe f p bt → rootLe f p (get_last bt).2 := by
  intro bt h
  cases bt with
  | leaf => simp [get_last, rootLe]
  | node l v r =>
      cases l <;> cases r <;> simp [get_last, rootLe] at h ⊢
      all_goals tauto

private theorem get_last_node_fst_some {α : Type u} :
    (l : BinaryTree α) → (y : α) → (r : BinaryTree α) →
      ∃ z : α, (get_last (node l y r)).1 = some z
  | leaf, y, leaf => by
      exact ⟨y, by simp [get_last]⟩
  | leaf, y, node rl rv rr => by
      rcases get_last_node_fst_some rl rv rr with ⟨z, hz⟩
      exact ⟨z, by simpa [get_last] using hz⟩
  | node ll lv lr, y, r => by
      rcases get_last_node_fst_some ll lv lr with ⟨z, hz⟩
      exact ⟨z, by simpa [get_last] using hz⟩
termination_by l _ r => sizeOf l + sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals simp [Nat.add_assoc]
  all_goals omega

private theorem contains_heapify_node {α : Type u} (f : α → ENat) :
    (l : BinaryTree α) → (y : α) → (r : BinaryTree α) →
    ∀ x : α, contains (heapify (node l y r) f) x ↔ contains (node l y r) x
  | leaf, y, leaf => by
      intro x
      simp [heapify, contains]
  | leaf, y, node rl rv rr => by
      intro x
      by_cases hrv : f rv < f y
      · have hrec := contains_heapify_node f rl y rr x
        simp [heapify, contains, hrv, hrec, or_left_comm]
      · simp [heapify, contains, hrv]
  | node ll lv lr, y, leaf => by
      intro x
      by_cases hlv : f lv < f y
      · have hrec := contains_heapify_node f ll y lr x
        simp [heapify, contains, hlv, hrec, or_left_comm]
      · simp [heapify, contains, hlv]
  | node ll lv lr, y, node rl rv rr => by
      intro x
      by_cases hlerv : f lv ≤ f rv
      · by_cases hyv : f y ≤ f lv
        · simp [heapify, contains, hlerv, hyv]
        · have hrec := contains_heapify_node f ll y lr x
          simp [heapify, contains, hlerv, hyv, hrec, or_assoc, or_left_comm]
      · by_cases hyr : f y ≤ f rv
        · simp [heapify, contains, hlerv, hyr]
        · have hrec := contains_heapify_node f rl y rr x
          simp [heapify, contains, hlerv, hyr, hrec, or_assoc, or_left_comm]
termination_by l _ r => sizeOf l + sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals simp [Nat.add_assoc]
  all_goals omega

private theorem contains_heapify_iff {α : Type u} (bt : BinaryTree α) (f : α → ENat) :
    ∀ x : α, contains (heapify bt f) x ↔ contains bt x := by
  intro x
  cases bt with
  | leaf => simp [heapify, contains]
  | node l y r => exact contains_heapify_node f l y r x

private theorem get_last_fst_contains {α : Type u} :
    ∀ (bt : BinaryTree α) (x : α), (get_last bt).1 = some x → contains bt x := by
  intro bt
  induction bt with
  | leaf =>
      intro x h
      simp [get_last] at h
  | node l y r ihl ihr =>
      intro x h
      cases l with
      | leaf =>
          cases r with
          | leaf =>
              have hyx : y = x := by simpa [get_last] using h
              exact Or.inl hyx
          | node rl rv rr =>
              have hr : contains (node rl rv rr) x := ihr x (by simpa [get_last] using h)
              exact Or.inr (Or.inr hr)
      | node ll lv lr =>
          have hl : contains (node ll lv lr) x := ihl x (by simpa [get_last] using h)
          exact Or.inr (Or.inl hl)

private theorem get_last_snd_subset {α : Type u} :
    ∀ (bt : BinaryTree α) (x : α), contains (get_last bt).2 x → contains bt x := by
  intro bt
  induction bt with
  | leaf =>
      intro x h
      simp [get_last, contains] at h
  | node l y r ihl ihr =>
      intro x h
      cases l with
      | leaf =>
          cases r with
          | leaf =>
              simp [get_last, contains] at h
          | node rl rv rr =>
              have hn : y = x ∨ contains (get_last (node rl rv rr)).2 x := by
                simpa [get_last, contains] using h
              rcases hn with hyx | hr
              · exact Or.inl hyx
              · exact Or.inr (Or.inr (ihr x hr))
      | node ll lv lr =>
          have hn : y = x ∨ contains (get_last (node ll lv lr)).2 x ∨ contains r x := by
            simpa [get_last, contains] using h
          rcases hn with hyx | hrest
          · exact Or.inl hyx
          · rcases hrest with hl | hr
            · exact Or.inr (Or.inl (ihl x hl))
            · exact Or.inr (Or.inr hr)

private theorem get_last_contains_split {α : Type u} :
    ∀ (bt : BinaryTree α) (last : α) (t : BinaryTree α) (x : α),
      get_last bt = (some last, t) → contains bt x → x = last ∨ contains t x := by
  intro bt
  induction bt with
  | leaf =>
      intro last t x hlast hcontains
      simp [get_last] at hlast
  | node l y r ihl ihr =>
      intro last t x hlast hcontains
      cases l with
      | leaf =>
          cases r with
          | leaf =>
              have hmain : get_last (node leaf y leaf) = (some y, leaf) := by simp [get_last]
              rw [hmain] at hlast
              cases hlast
              have hx : y = x := by simpa [contains] using hcontains
              exact Or.inl hx.symm
          | node rl rv rr =>
              cases hgr : get_last (node rl rv rr) with
              | mk val tree =>
                  have hmain :
                      get_last (node leaf y (node rl rv rr)) =
                        (val, node leaf y tree) := by
                    change
                      ((get_last (node rl rv rr)).1,
                        node leaf y (get_last (node rl rv rr)).2) =
                          (val, node leaf y tree)
                    rw [hgr]
                  rw [hmain] at hlast
                  cases val with
                  | none => cases hlast
                  | some z =>
                      have hzlast : z = last := by simpa using congrArg Prod.fst hlast
                      have htt : node leaf y tree = t := by simpa using congrArg Prod.snd hlast
                      have hy_or_hr : y = x ∨ contains (node rl rv rr) x := by
                        simpa [contains] using hcontains
                      rcases hy_or_hr with hyx | hrx
                      · exact Or.inr (by rw [← htt]; simp [contains, hyx])
                      · have hs := ihr z tree x hgr hrx
                        rcases hs with hxz | htree
                        · exact Or.inl (hxz.trans hzlast)
                        · exact Or.inr (by rw [← htt]; simp [contains, htree])
      | node ll lv lr =>
          cases hgl : get_last (node ll lv lr) with
          | mk val tree =>
              have hmain : get_last (node (node ll lv lr) y r) = (val, node tree y r) := by
                change ((get_last (node ll lv lr)).1, node (get_last (node ll lv lr)).2 y r) =
                  (val, node tree y r)
                rw [hgl]
              rw [hmain] at hlast
              cases val with
              | none => cases hlast
              | some z =>
                  have hzlast : z = last := by simpa using congrArg Prod.fst hlast
                  have htt : node tree y r = t := by simpa using congrArg Prod.snd hlast
                  have hy_or_rest : y = x ∨ contains (node ll lv lr) x ∨ contains r x := by
                    simpa [contains] using hcontains
                  rcases hy_or_rest with hyx | hrest
                  · exact Or.inr (by rw [← htt]; simp [contains, hyx])
                  · rcases hrest with hlx | hrx
                    · have hs := ihl z tree x hgl hlx
                      rcases hs with hxz | htree
                      · exact Or.inl (hxz.trans hzlast)
                      · exact Or.inr (by rw [← htt]; simp [contains, htree])
                    · exact Or.inr (by rw [← htt]; simp [contains, hrx])

private theorem extract_min_subset {α : Type u} (bt : BinaryTree α) (f : α → ENat) :
    ∀ x : α, contains (extract_min bt f).2 x → contains bt x := by
  intro x h
  cases hgl : get_last bt with
  | mk last t =>
      cases last with
      | none =>
          simp [extract_min, hgl, contains] at h
      | some y =>
          cases t with
          | leaf =>
              simp [extract_min, hgl, contains] at h
          | node l root r =>
              have hin : contains (node l y r) x :=
                (contains_heapify_iff (node l y r) f x).1 (by simpa [extract_min, hgl] using h)
              rcases hin with hyx | hrest
              · exact get_last_fst_contains bt x (by simp [hgl, hyx])
              · have ht : contains (node l root r) x := Or.inr hrest
                exact get_last_snd_subset bt x (by simpa [hgl] using ht)

private theorem extract_min_contains_nonroot_node {α : Type u}
    (l : BinaryTree α) (v : α) (r : BinaryTree α) (x : α) (f : α → ENat) :
    contains (node l v r) x → v ≠ x → contains (extract_min (node l v r) f).2 x := by
  intro hcontains hne
  cases l with
  | leaf =>
      cases r with
      | leaf =>
          have hvx : v = x := by simpa [contains] using hcontains
          exact False.elim (hne hvx)
      | node rl rv rr =>
          have hrx : contains (node rl rv rr) x := by
            have hsplit : v = x ∨ contains (node rl rv rr) x := by
              simpa [contains] using hcontains
            rcases hsplit with hvx | hrx
            · exact False.elim (hne hvx)
            · exact hrx
          cases hgr : get_last (node rl rv rr) with
          | mk last tree =>
              cases last with
              | none =>
                  rcases get_last_node_fst_some rl rv rr with ⟨z, hz⟩
                  simp [hgr] at hz
              | some z =>
                  have hs := get_last_contains_split (node rl rv rr) z tree x
                    (by simp [hgr]) hrx
                  have hpre : contains (node leaf z tree) x := by
                    rcases hs with hxz | htree
                    · exact Or.inl hxz.symm
                    · exact Or.inr (Or.inr htree)
                  have hget :
                      get_last (node leaf v (node rl rv rr)) =
                        (some z, node leaf v tree) := by
                    change
                      ((get_last (node rl rv rr)).1,
                        node leaf v (get_last (node rl rv rr)).2) =
                          (some z, node leaf v tree)
                    rw [hgr]
                  rw [show
                      (extract_min (node leaf v (node rl rv rr)) f).2 =
                        heapify (node leaf z tree) f by
                    simp [extract_min, hget]]
                  exact (contains_heapify_iff (node leaf z tree) f x).2 hpre
  | node ll lv lr =>
      have hrest : contains (node ll lv lr) x ∨ contains r x := by
        have hsplit : v = x ∨ contains (node ll lv lr) x ∨ contains r x := by
          simpa [contains] using hcontains
        rcases hsplit with hvx | hrest
        · exact False.elim (hne hvx)
        · exact hrest
      cases hgl : get_last (node ll lv lr) with
      | mk last tree =>
          cases last with
          | none =>
              rcases get_last_node_fst_some ll lv lr with ⟨z, hz⟩
              simp [hgl] at hz
          | some z =>
              have hpre : contains (node tree z r) x := by
                rcases hrest with hlx | hrx
                · have hs := get_last_contains_split (node ll lv lr) z tree x
                    (by simp [hgl]) hlx
                  rcases hs with hxz | htree
                  · exact Or.inl hxz.symm
                  · exact Or.inr (Or.inl htree)
                · exact Or.inr (Or.inr hrx)
              have hget : get_last (node (node ll lv lr) v r) = (some z, node tree v r) := by
                change ((get_last (node ll lv lr)).1, node (get_last (node ll lv lr)).2 v r) =
                  (some z, node tree v r)
                rw [hgl]
              rw [show (extract_min (node (node ll lv lr) v r) f).2 = heapify (node tree z r) f by
                simp [extract_min, hget]]
              exact (contains_heapify_iff (node tree z r) f x).2 hpre

private theorem get_last_snd_min_heap {α : Type u} (f : α → ENat) :
    ∀ (bt : BinaryTree α), is_min_heap bt f → is_min_heap (get_last bt).2 f := by
  intro bt
  induction bt with
  | leaf =>
      intro h
      simp [get_last, is_min_heap]
  | node l v r ihl ihr =>
      intro h
      have hlheap : is_min_heap l f := min_heap_left_of_node f l v r h
      have hrheap : is_min_heap r f := min_heap_right_of_node f l v r h
      have hlroot : rootLe f (f v) l := rootLe_left_of_node f l v r h
      have hrroot : rootLe f (f v) r := rootLe_right_of_node f l v r h
      cases l with
      | leaf =>
          cases r with
          | leaf =>
              simp [get_last, is_min_heap]
          | node rl rv rr =>
              have htreeheap : is_min_heap (get_last (node rl rv rr)).2 f := ihr hrheap
              have htreeroot : rootLe f (f v) (get_last (node rl rv rr)).2 :=
                rootLe_get_last_snd f (f v) (node rl rv rr) hrroot
              change is_min_heap (node leaf v (get_last (node rl rv rr)).2) f
              cases ht : (get_last (node rl rv rr)).2 with
              | leaf =>
                  simp [is_min_heap]
              | node tl tv tr =>
                  have hroot : f v ≤ f tv := by simpa [ht, rootLe] using htreeroot
                  have hheap : is_min_heap (node tl tv tr) f := by simpa [ht] using htreeheap
                  simpa [is_min_heap] using And.intro hroot hheap
      | node ll lv lr =>
          have htreeheap : is_min_heap (get_last (node ll lv lr)).2 f := ihl hlheap
          have htreeroot : rootLe f (f v) (get_last (node ll lv lr)).2 :=
            rootLe_get_last_snd f (f v) (node ll lv lr) hlroot
          change is_min_heap (node (get_last (node ll lv lr)).2 v r) f
          cases ht : (get_last (node ll lv lr)).2 with
          | leaf =>
              cases r with
              | leaf =>
                  simp [is_min_heap]
              | node rl rv rr =>
                  have hrootR : f v ≤ f rv := by simpa [rootLe] using hrroot
                  have hheapR : is_min_heap (node rl rv rr) f := hrheap
                  simpa [is_min_heap] using And.intro hrootR hheapR
          | node tl tv tr =>
              have hrootL : f v ≤ f tv := by simpa [ht, rootLe] using htreeroot
              have hheapL : is_min_heap (node tl tv tr) f := by simpa [ht] using htreeheap
              cases r with
              | leaf =>
                  simpa [is_min_heap] using And.intro hrootL hheapL
              | node rl rv rr =>
                  have hrootR : f v ≤ f rv := by simpa [rootLe] using hrroot
                  have hheapR : is_min_heap (node rl rv rr) f := hrheap
                  simpa [is_min_heap] using
                    And.intro hrootL (And.intro hheapL (And.intro hrootR hheapR))

private theorem heap_min_eq_root_of_min_heap {α : Type u} (f : α → ENat) :
    ∀ (l : BinaryTree α) (v : α) (r : BinaryTree α),
      is_min_heap (node l v r) f → f v = heap_min (node l v r) f := by
  intro l v r h
  cases l with
  | leaf =>
      cases r with
      | leaf => simp [heap_min]
      | node rl rv rr =>
          have hroot : f v ≤ f rv := rootLe_right_of_node f leaf v (node rl rv rr) h
          simp [heap_min, hroot]
  | node ll lv lr =>
      have hrootL : f v ≤ f lv := rootLe_left_of_node f (node ll lv lr) v r h
      cases r with
      | leaf =>
          simp [heap_min, hrootL]
      | node rl rv rr =>
          have hrootR : f v ≤ f rv := rootLe_right_of_node f (node ll lv lr) v (node rl rv rr) h
          by_cases hle : f lv ≤ f rv
          · simp [heap_min, hle, hrootL]
          · simp [heap_min, hle, hrootR]

private theorem extract_min_node_heap_correct {α : Type u} (f : α → ENat) :
    ∀ (l : BinaryTree α) (v : α) (r : BinaryTree α),
      is_min_heap (node l v r) f →
      ∃ bt' v', extract_min (node l v r) f = (some v', bt') ∧
        is_min_heap bt' f ∧ f v = heap_min (node l v r) f := by
  intro l v r hheap
  have hmin : f v = heap_min (node l v r) f := heap_min_eq_root_of_min_heap f l v r hheap
  cases l with
  | leaf =>
      cases r with
      | leaf =>
          exact ⟨leaf, v, by simp [extract_min, get_last], by simp [is_min_heap], hmin⟩
      | node rl rv rr =>
          have hrheap : is_min_heap (node rl rv rr) f :=
            min_heap_right_of_node f leaf v (node rl rv rr) hheap
          cases hgr : get_last (node rl rv rr) with
          | mk last tree =>
              cases last with
              | none =>
                  rcases get_last_node_fst_some rl rv rr with ⟨z, hz⟩
                  simp [hgr] at hz
              | some z =>
                  have htree : is_min_heap tree f := by
                    simpa [hgr] using get_last_snd_min_heap f (node rl rv rr) hrheap
                  have hnew : is_min_heap (heapify (node leaf z tree) f) f := by
                    exact (heapify_correctness (bt := node leaf z tree) (f := f)
                      (v := z) (l := leaf) (r := tree))
                      ⟨contains_heapify_iff (node leaf z tree) f z, rfl,
                        by simp [is_min_heap], htree⟩
                  have hget :
                      get_last (node leaf v (node rl rv rr)) =
                        (some z, node leaf v tree) := by
                    change
                      ((get_last (node rl rv rr)).1,
                        node leaf v (get_last (node rl rv rr)).2) =
                          (some z, node leaf v tree)
                    rw [hgr]
                  exact ⟨heapify (node leaf z tree) f, v,
                    by simp [extract_min, hget], hnew, hmin⟩
  | node ll lv lr =>
      have hlheap : is_min_heap (node ll lv lr) f :=
        min_heap_left_of_node f (node ll lv lr) v r hheap
      have hrheap : is_min_heap r f :=
        min_heap_right_of_node f (node ll lv lr) v r hheap
      cases hgl : get_last (node ll lv lr) with
      | mk last tree =>
          cases last with
          | none =>
              rcases get_last_node_fst_some ll lv lr with ⟨z, hz⟩
              simp [hgl] at hz
          | some z =>
              have htree : is_min_heap tree f := by
                simpa [hgl] using get_last_snd_min_heap f (node ll lv lr) hlheap
              have hnew : is_min_heap (heapify (node tree z r) f) f := by
                exact (heapify_correctness (bt := node tree z r) (f := f)
                  (v := z) (l := tree) (r := r))
                  ⟨contains_heapify_iff (node tree z r) f z, rfl, htree, hrheap⟩
              have hget : get_last (node (node ll lv lr) v r) = (some z, node tree v r) := by
                change ((get_last (node ll lv lr)).1, node (get_last (node ll lv lr)).2 v r) =
                  (some z, node tree v r)
                rw [hgl]
              exact ⟨heapify (node tree z r) f, v,
                by simp [extract_min, hget], hnew, hmin⟩

theorem extract_min_correctness (bt l r: BinaryTree α) (v v': α) (f: α → ENat): (
  contains (extract_min bt f).2 v → contains bt v)
  ∧ (bt = node l v r → contains bt v' → v ≠ v' → contains (extract_min bt f).2 v')
  ∧ (bt = node l v r → is_min_heap bt f → ∃ bt' v', extract_min bt f = (some v', bt')
  ∧ is_min_heap bt' f ∧ f v = heap_min bt f) := by
  constructor
  · intro h
    exact extract_min_subset bt f v h
  constructor
  · intro hbt hcontains hne
    subst bt
    exact extract_min_contains_nonroot_node l v r v' f hcontains hne
  · intro hbt hheap
    subst bt
    exact extract_min_node_heap_correct f l v r hheap
