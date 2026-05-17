/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

-- heapify_correctness:
-- This theorem bundles two key correctness properties of `heapify`:
-- 1) `heapify` preserves membership: an element is contained in `heapify bt f`
--    iff it was contained in `bt`.
-- 2) If `bt = node l v r` and both children `l` and `r` are min-heaps, then
--    `heapify bt f` is a min-heap. The proof combines containment lemmas and
--    `heapify_establishes_min_heap` which shows that fixing one violating
--    child yields a valid min-heap.
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

private theorem heapify_node_correct_aux {α : Type u} (f : α → ENat) :
    (l : BinaryTree α) → (v : α) → (r : BinaryTree α) →
    is_min_heap l f → is_min_heap r f →
    is_min_heap (heapify (node l v r) f) f ∧
      ∀ p, heapRootLe f p l → p ≤ f v → heapRootLe f p r →
        heapRootLe f p (heapify (node l v r) f)
  | leaf, v, leaf => by
      intro hl hr
      constructor
      · simp [heapify, is_min_heap]
      · intro p hpl hpv hpr
        simpa [heapify, heapRootLe] using hpv
  | leaf, v, node rl rv rr => by
      intro hl hr
      have hrec := heapify_node_correct_aux f rl v rr
        (is_min_heap_left_of_node (f := f) (l := rl) (v := rv) (r := rr) hr)
        (is_min_heap_right_of_node (f := f) (l := rl) (v := rv) (r := rr) hr)
      constructor
      · by_cases hrv : f rv < f v
        · have htroot : heapRootLe f (f rv) (heapify (node rl v rr) f) :=
            hrec.2 (f rv)
              (heapRootLe_left_of_min_heap (f := f) (l := rl) (v := rv) (r := rr) hr)
              (le_of_lt hrv)
              (heapRootLe_right_of_min_heap (f := f) (l := rl) (v := rv) (r := rr) hr)
          have htmin : is_min_heap (heapify (node rl v rr) f) f := hrec.1
          cases ht : heapify (node rl v rr) f with
          | leaf =>
              simp [heapify, hrv, ht, is_min_heap]
          | node tl tv tr =>
              have htroot' : f rv ≤ f tv := by
                simpa [ht, heapRootLe] using htroot
              have htmin' : is_min_heap (node tl tv tr) f := by
                simpa [ht] using htmin
              simpa [heapify, hrv, ht, is_min_heap] using
                (show f rv ≤ f tv ∧ is_min_heap (node tl tv tr) f from ⟨htroot', htmin'⟩)
        · have hle : f v ≤ f rv := le_of_not_gt hrv
          simpa [heapify, hrv, is_min_heap] using
            (show f v ≤ f rv ∧ is_min_heap (node rl rv rr) f from ⟨hle, hr⟩)
      · intro p hpl hpv hpr
        by_cases hrv : f rv < f v
        · simpa [heapify, hrv, heapRootLe] using hpr
        · simpa [heapify, hrv, heapRootLe] using hpv
  | node ll lv lr, v, leaf => by
      intro hl hr
      have hrec := heapify_node_correct_aux f ll v lr
        (is_min_heap_left_of_node (f := f) (l := ll) (v := lv) (r := lr) hl)
        (is_min_heap_right_of_node (f := f) (l := ll) (v := lv) (r := lr) hl)
      constructor
      · by_cases hlv : f lv < f v
        · have htroot : heapRootLe f (f lv) (heapify (node ll v lr) f) :=
            hrec.2 (f lv)
              (heapRootLe_left_of_min_heap (f := f) (l := ll) (v := lv) (r := lr) hl)
              (le_of_lt hlv)
              (heapRootLe_right_of_min_heap (f := f) (l := ll) (v := lv) (r := lr) hl)
          have htmin : is_min_heap (heapify (node ll v lr) f) f := hrec.1
          cases ht : heapify (node ll v lr) f with
          | leaf =>
              simp [heapify, hlv, ht, is_min_heap]
          | node tl tv tr =>
              have htroot' : f lv ≤ f tv := by
                simpa [ht, heapRootLe] using htroot
              have htmin' : is_min_heap (node tl tv tr) f := by
                simpa [ht] using htmin
              simpa [heapify, hlv, ht, is_min_heap] using
                (show f lv ≤ f tv ∧ is_min_heap (node tl tv tr) f from ⟨htroot', htmin'⟩)
        · have hle : f v ≤ f lv := le_of_not_gt hlv
          simpa [heapify, hlv, is_min_heap] using
            (show f v ≤ f lv ∧ is_min_heap (node ll lv lr) f from ⟨hle, hl⟩)
      · intro p hpl hpv hpr
        by_cases hlv : f lv < f v
        · simpa [heapify, hlv, heapRootLe] using hpl
        · simpa [heapify, hlv, heapRootLe] using hpv
  | node ll lv lr, v, node rl rv rr => by
      intro hl hr
      have recL := heapify_node_correct_aux f ll v lr
        (is_min_heap_left_of_node (f := f) (l := ll) (v := lv) (r := lr) hl)
        (is_min_heap_right_of_node (f := f) (l := ll) (v := lv) (r := lr) hl)
      have recR := heapify_node_correct_aux f rl v rr
        (is_min_heap_left_of_node (f := f) (l := rl) (v := rv) (r := rr) hr)
        (is_min_heap_right_of_node (f := f) (l := rl) (v := rv) (r := rr) hr)
      constructor
      · by_cases hlerv : f lv ≤ f rv
        · by_cases hvlel : f v ≤ f lv
          · have hvler : f v ≤ f rv := le_trans hvlel hlerv
            simpa [heapify, hlerv, hvlel, is_min_heap] using
              (show f v ≤ f lv ∧ is_min_heap (node ll lv lr) f ∧
                  f v ≤ f rv ∧ is_min_heap (node rl rv rr) f from
                ⟨hvlel, hl, hvler, hr⟩)
          · have hltv : f lv < f v := lt_of_not_ge hvlel
            have htroot : heapRootLe f (f lv) (heapify (node ll v lr) f) :=
              recL.2 (f lv)
                (heapRootLe_left_of_min_heap (f := f) (l := ll) (v := lv) (r := lr) hl)
                (le_of_lt hltv)
                (heapRootLe_right_of_min_heap (f := f) (l := ll) (v := lv) (r := lr) hl)
            have htmin : is_min_heap (heapify (node ll v lr) f) f := recL.1
            cases ht : heapify (node ll v lr) f with
            | leaf =>
                simpa [heapify, hlerv, hvlel, ht, is_min_heap] using
                  (show f lv ≤ f rv ∧ is_min_heap (node rl rv rr) f from ⟨hlerv, hr⟩)
            | node tl tv tr =>
                have htroot' : f lv ≤ f tv := by
                  simpa [ht, heapRootLe] using htroot
                have htmin' : is_min_heap (node tl tv tr) f := by
                  simpa [ht] using htmin
                simpa [heapify, hlerv, hvlel, ht, is_min_heap] using
                  (show f lv ≤ f tv ∧ is_min_heap (node tl tv tr) f ∧
                      f lv ≤ f rv ∧ is_min_heap (node rl rv rr) f from
                    ⟨htroot', htmin', hlerv, hr⟩)
        · have hrvltlv : f rv < f lv := lt_of_not_ge hlerv
          by_cases hvler : f v ≤ f rv
          · have hvlel : f v ≤ f lv := le_trans hvler (le_of_lt hrvltlv)
            simpa [heapify, hlerv, hvler, is_min_heap] using
              (show f v ≤ f lv ∧ is_min_heap (node ll lv lr) f ∧
                  f v ≤ f rv ∧ is_min_heap (node rl rv rr) f from
                ⟨hvlel, hl, hvler, hr⟩)
          · have hrltv : f rv < f v := lt_of_not_ge hvler
            have htroot : heapRootLe f (f rv) (heapify (node rl v rr) f) :=
              recR.2 (f rv)
                (heapRootLe_left_of_min_heap (f := f) (l := rl) (v := rv) (r := rr) hr)
                (le_of_lt hrltv)
                (heapRootLe_right_of_min_heap (f := f) (l := rl) (v := rv) (r := rr) hr)
            have htmin : is_min_heap (heapify (node rl v rr) f) f := recR.1
            cases ht : heapify (node rl v rr) f with
            | leaf =>
                simpa [heapify, hlerv, hvler, ht, is_min_heap] using
                  (show f rv ≤ f lv ∧ is_min_heap (node ll lv lr) f from
                    ⟨le_of_lt hrvltlv, hl⟩)
            | node tl tv tr =>
                have htroot' : f rv ≤ f tv := by
                  simpa [ht, heapRootLe] using htroot
                have htmin' : is_min_heap (node tl tv tr) f := by
                  simpa [ht] using htmin
                simpa [heapify, hlerv, hvler, ht, is_min_heap] using
                  (show f rv ≤ f lv ∧ is_min_heap (node ll lv lr) f ∧
                      f rv ≤ f tv ∧ is_min_heap (node tl tv tr) f from
                    ⟨le_of_lt hrvltlv, hl, htroot', htmin'⟩)
      · intro p hpl hpv hpr
        by_cases hlerv : f lv ≤ f rv
        · by_cases hvlel : f v ≤ f lv
          · simpa [heapify, hlerv, hvlel, heapRootLe] using hpv
          · simpa [heapify, hlerv, hvlel, heapRootLe] using hpl
        · by_cases hvler : f v ≤ f rv
          · simpa [heapify, hlerv, hvler, heapRootLe] using hpv
          · simpa [heapify, hlerv, hvler, heapRootLe] using hpr
termination_by l _ r => sizeOf l + sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals simp [Nat.add_assoc, Nat.add_left_comm]
  all_goals omega

theorem heapify_correctness (bt: BinaryTree α) (f: α → ENat):
  (contains (heapify bt f) v ↔ contains bt v) ∧
  bt = node l v r ∧ is_min_heap l f ∧ is_min_heap r f → is_min_heap (heapify bt f) f := by
  intro h
  rcases h with ⟨_, hbt, hl, hr⟩
  subst bt
  exact (heapify_node_correct_aux f l v r hl hr).1
