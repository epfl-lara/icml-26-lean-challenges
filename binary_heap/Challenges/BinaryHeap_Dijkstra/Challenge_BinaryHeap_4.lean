/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

-- decrease_priority_correctness:
-- States the two main correctness properties of `decrease_priority`:
-- - Membership preservation/behavior: an element `v` is in the original tree
--   exactly when it is in the tree after calling `decrease_priority bt v' f`.
--   In other words, decreasing the priority does not lose or create elements.
-- - Heap preservation: if the original `bt` is a min-heap, then decreasing
--   the priority of a value preserves the min-heap property.
-- The proof combines the containment lemmas and the preservation lemma above.
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
      simpa only [BinaryTree.insert, BinaryTree.contains, Bool.false_eq_true,
        false_or, or_false] using (eq_comm : v' = v ↔ v = v')
  | node l x r ihl ihr =>
      intro v v'
      by_cases hle : f v' ≤ f x
      · simp [BinaryTree.insert, BinaryTree.contains, hle, ihl, eq_comm,
          or_assoc, or_left_comm, or_comm]
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
        · have ihx := ihl x hl
          have hleftRootX : heapRootLe f (f x) l :=
            heapRootLe_left_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap
          have hrightRootX : heapRootLe f (f x) r :=
            heapRootLe_right_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap
          have hleftRoot : heapRootLe f (f v) (insert l x f) :=
            ihx.2 (f v) (heapRootLe_mono (f := f) hle hleftRootX) hle
          have hrightRoot : heapRootLe f (f v) r :=
            heapRootLe_mono (f := f) hle hrightRootX
          simpa [BinaryTree.insert, hle] using
            (is_min_heap_node_of_rootLe (f := f) (l := insert l x f) (r := r) (v := v)
              ihx.1 hr hleftRoot hrightRoot)
        · have hxv : f x ≤ f v := le_of_lt (lt_of_not_ge hle)
          have ihv := ihl v hl
          have hleftRootX : heapRootLe f (f x) l :=
            heapRootLe_left_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap
          have hrightRoot : heapRootLe f (f x) r :=
            heapRootLe_right_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap
          have hleftRoot : heapRootLe f (f x) (insert l v f) :=
            ihv.2 (f x) hleftRootX hxv
          simpa [BinaryTree.insert, hle] using
            (is_min_heap_node_of_rootLe (f := f) (l := insert l v f) (r := r) (v := x)
              ihv.1 hr hleftRoot hrightRoot)
      · intro p hpbt hpv
        by_cases hle : f v ≤ f x
        · simpa [BinaryTree.insert, hle, heapRootLe] using hpv
        · have hpx : p ≤ f x := by
            simpa [heapRootLe] using hpbt
          simpa [BinaryTree.insert, hle, heapRootLe] using hpx

private theorem containsb_eq_contains {α : Type u} [DecidableEq α]
    (bt : BinaryTree α) : ∀ v : α, containsb bt v = true ↔ contains bt v := by
  induction bt with
  | leaf =>
      intro v
      simp [BinaryTree.containsb, BinaryTree.contains, Bool.false_eq_true]
  | node l x r ihl ihr =>
      intro v
      by_cases hxv : x = v
      · simp [BinaryTree.containsb, BinaryTree.contains, hxv]
      · simp [BinaryTree.containsb, BinaryTree.contains, hxv, ihl v, ihr v]

private theorem contains_merge {α : Type u} (f : α → ENat) :
    (t₁ t₂ : BinaryTree α) → ∀ v : α,
      contains (merge t₁ t₂ f) v ↔ contains t₁ v ∨ contains t₂ v
  | leaf, t₂ => by
      intro v
      simp [BinaryTree.merge, BinaryTree.contains, Bool.false_eq_true]
  | node l₁ x₁ r₁, leaf => by
      intro v
      simp [BinaryTree.merge, BinaryTree.contains, Bool.false_eq_true]
  | node l₁ x₁ r₁, node l₂ x₂ r₂ => by
      intro v
      by_cases hle : f x₁ ≤ f x₂
      · have hrec := contains_merge f l₁ (node l₂ x₂ r₂) v
        simp [BinaryTree.merge, BinaryTree.contains, hle, hrec,
          or_assoc, or_left_comm, or_comm]
      · have hrec := contains_merge f (node l₁ x₁ r₁) l₂ v
        simp [BinaryTree.merge, BinaryTree.contains, hle, hrec,
          or_assoc, or_left_comm]
termination_by t₁ t₂ => sizeOf t₁ + sizeOf t₂
decreasing_by
  all_goals simp_wf
  all_goals simp [Nat.add_assoc]
  all_goals omega

private theorem contains_remove_subset {α : Type u} [DecidableEq α]
    (bt : BinaryTree α) (f : α → ENat) :
    ∀ v y : α, contains (remove bt y f) v → contains bt v := by
  induction bt with
  | leaf =>
      intro v y h
      exact h
  | node l x r ihl ihr =>
      intro v y h
      by_cases hyx : y = x
      · have hm : contains (merge l r f) v := by
          simpa [BinaryTree.remove, hyx] using h
        have hmr := (contains_merge f l r v).1 hm
        rcases hmr with hlv | hrv
        · exact Or.inr (Or.inl hlv)
        · exact Or.inr (Or.inr hrv)
      · have hn : x = v ∨ contains (remove l y f) v ∨ contains (remove r y f) v := by
          simpa [BinaryTree.remove, BinaryTree.contains, hyx] using h
        rcases hn with hxv | hlr
        · exact Or.inl hxv
        · rcases hlr with hlv | hrv
          · exact Or.inr (Or.inl (ihl v y hlv))
          · exact Or.inr (Or.inr (ihr v y hrv))

private theorem contains_remove_or_eq {α : Type u} [DecidableEq α]
    (bt : BinaryTree α) (f : α → ENat) :
    ∀ v y : α, contains bt v → contains (remove bt y f) v ∨ v = y := by
  induction bt with
  | leaf =>
      intro v y h
      cases h
  | node l x r ihl ihr =>
      intro v y h
      have hn : x = v ∨ contains l v ∨ contains r v := by
        simpa [BinaryTree.contains] using h
      by_cases hyx : y = x
      · rcases hn with hxv | hlr
        · exact Or.inr (hxv.symm.trans hyx.symm)
        · have hm : contains (merge l r f) v := by
            exact (contains_merge f l r v).2 hlr
          exact Or.inl (by simpa [BinaryTree.remove, hyx] using hm)
      · rcases hn with hxv | hlr
        · have hroot : contains (node (remove l y f) x (remove r y f)) v :=
            Or.inl hxv
          exact Or.inl (by simpa [BinaryTree.remove, hyx] using hroot)
        · rcases hlr with hlv | hrv
          · rcases ihl v y hlv with hlrem | hvy
            · have hnode : contains (node (remove l y f) x (remove r y f)) v :=
                Or.inr (Or.inl hlrem)
              exact Or.inl (by simpa [BinaryTree.remove, hyx] using hnode)
            · exact Or.inr hvy
          · rcases ihr v y hrv with hrrem | hvy
            · have hnode : contains (node (remove l y f) x (remove r y f)) v :=
                Or.inr (Or.inr hrrem)
              exact Or.inl (by simpa [BinaryTree.remove, hyx] using hnode)
            · exact Or.inr hvy

private theorem contains_insert_remove_of_contains {α : Type u} [DecidableEq α]
    (bt : BinaryTree α) (f : α → ENat) :
    ∀ v y : α, contains bt y →
      (contains (insert (remove bt y f) y f) v ↔ contains bt v) := by
  intro v y hy
  constructor
  · intro h
    have hi := (contains_insert (remove bt y f) f v y).1 h
    rcases hi with hrem | hvy
    · exact contains_remove_subset bt f v y hrem
    · simpa [hvy] using hy
  · intro hv
    have hr := contains_remove_or_eq bt f v y hv
    apply (contains_insert (remove bt y f) f v y).2
    exact hr

private theorem contains_decrease_priority {α : Type u} [DecidableEq α]
    (bt : BinaryTree α) (f : α → ENat) :
    ∀ v y : α, contains (decrease_priority bt y f) v ↔ contains bt v := by
  intro v y
  by_cases hcy : containsb bt y
  · have hy : contains bt y := (containsb_eq_contains bt y).1 hcy
    simpa [BinaryTree.decrease_priority, hcy] using
      (contains_insert_remove_of_contains bt f v y hy)
  · simp [BinaryTree.decrease_priority, hcy]

private theorem merge_heap_correct_aux {α : Type u} (f : α → ENat)
    (t₁ t₂ : BinaryTree α) :
    is_min_heap t₁ f → is_min_heap t₂ f →
      is_min_heap (merge t₁ t₂ f) f ∧
        ∀ p, heapRootLe f p t₁ → heapRootLe f p t₂ →
          heapRootLe f p (merge t₁ t₂ f) := by
  revert t₂
  induction t₁ with
  | leaf =>
      intro t₂ h₁ h₂
      constructor
      · simpa [BinaryTree.merge] using h₂
      · intro p hp₁ hp₂
        simpa [BinaryTree.merge] using hp₂
  | node l₁ x₁ r₁ ihl₁ ihr₁ =>
      intro t₂
      induction t₂ with
      | leaf =>
          intro h₁ h₂
          constructor
          · simpa [BinaryTree.merge] using h₁
          · intro p hp₁ hp₂
            simpa [BinaryTree.merge] using hp₁
      | node l₂ x₂ r₂ ihl₂ ihr₂ =>
          intro h₁ h₂
          have hl₁ : is_min_heap l₁ f :=
            is_min_heap_left_of_node (f := f) (l := l₁) (v := x₁) (r := r₁) h₁
          have hr₁ : is_min_heap r₁ f :=
            is_min_heap_right_of_node (f := f) (l := l₁) (v := x₁) (r := r₁) h₁
          have hl₂ : is_min_heap l₂ f :=
            is_min_heap_left_of_node (f := f) (l := l₂) (v := x₂) (r := r₂) h₂
          have hr₂ : is_min_heap r₂ f :=
            is_min_heap_right_of_node (f := f) (l := l₂) (v := x₂) (r := r₂) h₂
          by_cases hle : f x₁ ≤ f x₂
          · have hmerge := ihl₁ (node l₂ x₂ r₂) hl₁ h₂
            constructor
            · have hleftRoot : heapRootLe f (f x₁) (merge l₁ (node l₂ x₂ r₂) f) :=
                hmerge.2 (f x₁)
                  (heapRootLe_left_of_min_heap (f := f) (l := l₁) (v := x₁) (r := r₁) h₁)
                  (by simpa [heapRootLe] using hle)
              have hrightRoot : heapRootLe f (f x₁) r₁ :=
                heapRootLe_right_of_min_heap (f := f) (l := l₁) (v := x₁) (r := r₁) h₁
              simpa [BinaryTree.merge, hle] using
                (is_min_heap_node_of_rootLe (f := f)
                  (l := merge l₁ (node l₂ x₂ r₂) f) (r := r₁) (v := x₁)
                  hmerge.1 hr₁ hleftRoot hrightRoot)
            · intro p hp₁ hp₂
              simpa [BinaryTree.merge, hle, heapRootLe] using hp₁
          · have hx₂x₁ : f x₂ ≤ f x₁ := le_of_lt (lt_of_not_ge hle)
            have hmerge := ihl₂ h₁ hl₂
            constructor
            · have hleftRoot : heapRootLe f (f x₂) (merge (node l₁ x₁ r₁) l₂ f) :=
                hmerge.2 (f x₂)
                  (by simpa [heapRootLe] using hx₂x₁)
                  (heapRootLe_left_of_min_heap (f := f) (l := l₂) (v := x₂) (r := r₂) h₂)
              have hrightRoot : heapRootLe f (f x₂) r₂ :=
                heapRootLe_right_of_min_heap (f := f) (l := l₂) (v := x₂) (r := r₂) h₂
              simpa [BinaryTree.merge, hle] using
                (is_min_heap_node_of_rootLe (f := f)
                  (l := merge (node l₁ x₁ r₁) l₂ f) (r := r₂) (v := x₂)
                  hmerge.1 hr₂ hleftRoot hrightRoot)
            · intro p hp₁ hp₂
              simpa [BinaryTree.merge, hle, heapRootLe] using hp₂

private theorem remove_heap_correct_aux {α : Type u} [DecidableEq α]
    (f : α → ENat) :
    (bt : BinaryTree α) → ∀ y : α, is_min_heap bt f →
      is_min_heap (remove bt y f) f ∧
        ∀ p, heapRootLe f p bt → heapRootLe f p (remove bt y f)
  | leaf => by
      intro y hheap
      constructor
      · simp [BinaryTree.remove, is_min_heap]
      · intro p hp
        simp [BinaryTree.remove, heapRootLe]
  | node l x r => by
      intro y hheap
      have hl : is_min_heap l f :=
        is_min_heap_left_of_node (f := f) (l := l) (v := x) (r := r) hheap
      have hr : is_min_heap r f :=
        is_min_heap_right_of_node (f := f) (l := l) (v := x) (r := r) hheap
      by_cases hyx : y = x
      · have m := merge_heap_correct_aux f l r hl hr
        constructor
        · simpa [BinaryTree.remove, hyx] using m.1
        · intro p hpnode
          have hpx : p ≤ f x := by
            simpa [heapRootLe] using hpnode
          have hpl : heapRootLe f p l :=
            heapRootLe_mono (f := f) hpx
              (heapRootLe_left_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap)
          have hpr : heapRootLe f p r :=
            heapRootLe_mono (f := f) hpx
              (heapRootLe_right_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap)
          simpa [BinaryTree.remove, hyx] using m.2 p hpl hpr
      · have recL := remove_heap_correct_aux f l y hl
        have recR := remove_heap_correct_aux f r y hr
        constructor
        · have hleftRoot : heapRootLe f (f x) (remove l y f) :=
            recL.2 (f x)
              (heapRootLe_left_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap)
          have hrightRoot : heapRootLe f (f x) (remove r y f) :=
            recR.2 (f x)
              (heapRootLe_right_of_min_heap (f := f) (l := l) (v := x) (r := r) hheap)
          simpa [BinaryTree.remove, hyx] using
            (is_min_heap_node_of_rootLe (f := f)
              (l := remove l y f) (r := remove r y f) (v := x)
              recL.1 recR.1 hleftRoot hrightRoot)
        · intro p hpnode
          have hpx : p ≤ f x := by
            simpa [heapRootLe] using hpnode
          simpa [BinaryTree.remove, hyx, heapRootLe] using hpx

private theorem decrease_priority_heap {α : Type u} [DecidableEq α]
    (bt : BinaryTree α) (f : α → ENat) :
    ∀ y : α, is_min_heap bt f → is_min_heap (decrease_priority bt y f) f := by
  intro y hheap
  by_cases hcy : containsb bt y
  · have hremove : is_min_heap (remove bt y f) f :=
      (remove_heap_correct_aux f bt y hheap).1
    have hins : is_min_heap (insert (remove bt y f) y f) f :=
      (insert_heap_correct_aux (remove bt y f) f y hremove).1
    simpa [BinaryTree.decrease_priority, hcy] using hins
  · simpa [BinaryTree.decrease_priority, hcy] using hheap

lemma decrease_priority_correctness [DecidableEq α] (bt: BinaryTree α) (v v': α) (f : α → ENat):
  contains bt v ↔ contains (decrease_priority bt v' f) v ∧
  (is_min_heap bt f → is_min_heap (decrease_priority bt v f) f) := by
  constructor
  · intro hv
    constructor
    · exact (contains_decrease_priority bt f v v').2 hv
    · exact decrease_priority_heap bt f v
  · intro h
    exact (contains_decrease_priority bt f v v').1 h.1
