/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeapComposite

open BinaryTree BinaryHeap Finset SimpleGraph

set_option autoImplicit true

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
  Prove that the algotithm below terminates.
-/
theorem dijkstra_terminate {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V]
    [inst_2 : Nonempty V] (g : fin_simple_graph V) (dist : V → ℕ∞) (queue : BinaryHeap V)
    (hq hne : ¬queue.isEmpty = true) :
    (relax_neighbors g (queue.extract_min dist hne).1 dist (queue.extract_min dist hne).2).2.sizeOf <
      queue.sizeOf := by
  have _ := inst_2
  have _ := hq
  have heapify_size :
      ∀ (t : BinaryTree V) (p : V → ENat), (BinaryTree.heapify t p).size = t.size := by
    intro t p
    fun_induction BinaryTree.heapify t p <;> simp [BinaryTree.size, *]
  have insert_size :
      ∀ (t : BinaryTree V) (v : V) (p : V → ENat),
        (BinaryTree.insert t v p).size = t.size + 1 := by
    intro t v p
    induction t generalizing v with
    | leaf =>
      simp [BinaryTree.insert, BinaryTree.size]
    | node l x r ihl ihr =>
      by_cases h : p v ≤ p x <;> simp [BinaryTree.insert, BinaryTree.size, h, ihl] <;> omega
  have merge_size :
      ∀ (t₁ t₂ : BinaryTree V) (p : V → ENat),
        (BinaryTree.merge t₁ t₂ p).size = t₁.size + t₂.size := by
    intro t₁ t₂ p
    fun_induction BinaryTree.merge t₁ t₂ p <;> simp [BinaryTree.size, *] <;> omega
  have remove_size_le :
      ∀ (t : BinaryTree V) (x : V) (p : V → ENat),
        (BinaryTree.remove t x p).size ≤ t.size := by
    intro t x p
    induction t generalizing x p with
    | leaf =>
      simp [BinaryTree.remove, BinaryTree.size]
    | node l v r ihl ihr =>
      by_cases hx : x = v
      · simp [BinaryTree.remove, hx, merge_size, BinaryTree.size]
      · have hl := ihl x p
        have hr := ihr x p
        simp [BinaryTree.remove, hx, BinaryTree.size]
        omega
  have remove_size_lt_of_containsb :
      ∀ (t : BinaryTree V) (x : V) (p : V → ENat),
        BinaryTree.containsb t x = true → (BinaryTree.remove t x p).size < t.size := by
    intro t x p h
    induction t generalizing x p with
    | leaf =>
      simp [BinaryTree.containsb] at h
    | node l v r ihl ihr =>
      by_cases hx : x = v
      · simp [BinaryTree.remove, hx, merge_size, BinaryTree.size]
      · have hvx : v ≠ x := by intro h; exact hx h.symm
        have hmem : BinaryTree.containsb l x = true ∨ BinaryTree.containsb r x = true := by
          simpa [BinaryTree.containsb, hvx, Bool.or_eq_true] using h
        have hl_le := remove_size_le l x p
        have hr_le := remove_size_le r x p
        cases hmem with
        | inl hl =>
          have hl_lt := ihl x p hl
          simp [BinaryTree.remove, hx, BinaryTree.size]
          omega
        | inr hr =>
          have hr_lt := ihr x p hr
          simp [BinaryTree.remove, hx, BinaryTree.size]
          omega
  have decrease_tree_size_le :
      ∀ (t : BinaryTree V) (x : V) (p : V → ENat),
        (BinaryTree.decrease_priority t x p).size ≤ t.size := by
    intro t x p
    by_cases hcontains : BinaryTree.containsb t x = true
    · have hremove_lt := remove_size_lt_of_containsb t x p hcontains
      have hinsert := insert_size (BinaryTree.remove t x p) x p
      simp [BinaryTree.decrease_priority, hcontains, hinsert]
      omega
    · simp [BinaryTree.decrease_priority, hcontains]
  have decrease_heap_size_le :
      ∀ (q : BinaryHeap V) (x : V) (p : V → ENat),
        (q.decrease_priority x p).sizeOf ≤ q.sizeOf := by
    intro q x p
    rcases q with ⟨t⟩
    simpa [BinaryHeap.decrease_priority, BinaryHeap.sizeOf] using decrease_tree_size_le t x p
  have get_last_size :
      ∀ (t : BinaryTree V), t ≠ BinaryTree.leaf → (BinaryTree.get_last t).2.size + 1 = t.size := by
    intro t ht
    induction t with
    | leaf =>
      contradiction
    | node l v r ihl ihr =>
      cases l with
      | leaf =>
        cases r with
        | leaf =>
          simp [BinaryTree.get_last, BinaryTree.size]
        | node rl rv rr =>
          have hne : BinaryTree.node rl rv rr ≠ BinaryTree.leaf := by intro h; cases h
          have hr := ihr hne
          calc
            (BinaryTree.get_last (BinaryTree.node BinaryTree.leaf v (BinaryTree.node rl rv rr))).2.size + 1
                = (BinaryTree.node BinaryTree.leaf v
                    (BinaryTree.get_last (BinaryTree.node rl rv rr)).2).size + 1 := by
                    rfl
            _ = ((BinaryTree.get_last (BinaryTree.node rl rv rr)).2.size + 1) + 1 := by
                    simp [BinaryTree.size]
                    omega
            _ = (BinaryTree.node rl rv rr).size + 1 := by
                    rw [hr]
            _ = (BinaryTree.node BinaryTree.leaf v (BinaryTree.node rl rv rr)).size := by
                    simp [BinaryTree.size]
                    omega
      | node ll lv lr =>
        have hne : BinaryTree.node ll lv lr ≠ BinaryTree.leaf := by intro h; cases h
        have hl := ihl hne
        calc
          (BinaryTree.get_last (BinaryTree.node (BinaryTree.node ll lv lr) v r)).2.size + 1
              = (BinaryTree.node (BinaryTree.get_last (BinaryTree.node ll lv lr)).2 v r).size + 1 := by
                  rfl
          _ = ((BinaryTree.get_last (BinaryTree.node ll lv lr)).2.size + 1) + r.size + 1 := by
                  simp [BinaryTree.size]
                  omega
          _ = (BinaryTree.node ll lv lr).size + r.size + 1 := by
                  rw [hl]
          _ = (BinaryTree.node (BinaryTree.node ll lv lr) v r).size := by
                  simp [BinaryTree.size]
                  omega
  have extract_tree_size_lt :
      ∀ (t : BinaryTree V) (p : V → ENat),
        t ≠ BinaryTree.leaf → (BinaryTree.extract_min t p).2.size < t.size := by
    intro t p ht
    have tree_size_pos : 0 < t.size := by
      cases t with
      | leaf =>
        contradiction
      | node l v r =>
        simp [BinaryTree.size]
    unfold BinaryTree.extract_min
    cases hlast : BinaryTree.get_last t with
    | mk lastNode treeWithoutLast =>
      have hlast_size := get_last_size t ht
      simp [hlast] at hlast_size
      cases lastNode with
      | none =>
        simp [BinaryTree.size]
        exact tree_size_pos
      | some v =>
        cases treeWithoutLast with
        | leaf =>
          simp [BinaryTree.size]
          omega
        | node l w r =>
          have hheap := heapify_size (BinaryTree.node l v r) p
          have hshape : (BinaryTree.node l v r).size = (BinaryTree.node l w r).size := by
            simp [BinaryTree.size]
          rw [hheap, hshape]
          omega
  have extract_heap_size_lt :
      ∀ (q : BinaryHeap V) (p : V → ENat) (hne : ¬q.isEmpty = true),
        (q.extract_min p hne).2.sizeOf < q.sizeOf := by
    intro q p hne
    rcases q with ⟨t⟩
    have ht : t ≠ BinaryTree.leaf := by
      cases t with
      | leaf =>
        simp [BinaryHeap.isEmpty] at hne
      | node l v r =>
        intro h
        cases h
    simpa [BinaryHeap.extract_min, BinaryHeap.sizeOf] using extract_tree_size_lt t p ht
  have relax_neighbors_size_le :
      ∀ (g : fin_simple_graph V) (u : V) (dist : V → ENat) (q : BinaryHeap V),
        (relax_neighbors g u dist q).2.sizeOf ≤ q.sizeOf := by
    have fold_size_le :
        ∀ (xs : List V) (u : V) (dist : V → ENat) (q : BinaryHeap V),
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
            (dist, q) xs).2.sizeOf ≤ q.sizeOf := by
      intro xs u dist q
      induction xs generalizing dist q with
      | nil =>
        simp
      | cons v xs ih =>
        by_cases hlt : dist u + 1 < dist v
        · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
          have hdec : (q.decrease_priority v dist').sizeOf ≤ q.sizeOf :=
            decrease_heap_size_le q v dist'
          have hih := ih dist' (q.decrease_priority v dist')
          simp [List.foldl, hlt]
          exact le_trans hih hdec
        · have hih := ih dist q
          simpa [List.foldl, hlt] using hih
    intro g u dist q
    simpa [relax_neighbors] using fold_size_le (g.neighborFinset u).val.toList u dist q
  exact lt_of_le_of_lt
    (relax_neighbors_size_le g (queue.extract_min dist hne).1 dist (queue.extract_min dist hne).2)
    (extract_heap_size_lt queue dist hne)
