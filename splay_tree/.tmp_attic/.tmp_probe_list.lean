import Challenges.Splay_Tree.Def_Splay

example {α : Type} (done future : List α) (i : α) (b : Fin future.length) :
    (done ++ i :: future).get ⟨done.length + 1 + b.val, by
      have hb := b.isLt
      simp
      omega⟩ = future.get b := by
  rcases b with ⟨bv, hbv⟩
  simp [Nat.add_assoc]
  have hs : bv + 1 < (i :: future).length := by
    simpa [Nat.add_comm] using Nat.succ_lt_succ hbv
  simpa [Nat.add_comm] using (List.getElem_cons_succ i future bv hs)
