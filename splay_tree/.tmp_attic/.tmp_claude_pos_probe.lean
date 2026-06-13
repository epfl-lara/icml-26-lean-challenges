import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

open List in
example : True := trivial

#check @List.idxOf_cons_self
#check @List.idxOf_cons_ne
#check @List.take_succ_cons
#check @List.Nodup.of_append_left
#check @List.nodup_append
#check @List.dropLast_append_getLast
#check @List.getLast_mem
#check @List.dropLast_subset
#check @List.mem_append_left
#check @List.disjoint_left

example : ([3, 5] : List Nat).idxOf 3 = 0 := by simp
example : ([3, 5] : List Nat).idxOf 5 = 1 := by simp [List.idxOf_cons_ne]
example (l : List Nat) (a : Nat) : (a :: l).idxOf a = 0 := List.idxOf_cons_self ..
example (l : List Nat) (a b : Nat) (h : a ≠ b) : (b :: l).idxOf a = l.idxOf a + 1 := by
  rw [List.idxOf_cons_ne _ h]
