import Challenges.Splay_Tree.Def_Ackermann

namespace ProbeM12

def blkInd (group : List (List ℕ)) (a i : ℕ) : ℕ :=
  if a ∈ group.getD i [] then 1 else 0

theorem hsum_test (group : List (List ℕ)) (a b : ℕ) :
    (∑ i ∈ Finset.range group.length,
      blkInd group a i * blkInd group b i)
      = ((Finset.range group.length).filter
          (fun i => a ∈ group.getD i [] ∧ b ∈ group.getD i [])).card := by
  classical
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  unfold blkInd
  by_cases ha : a ∈ group.getD i []
  · by_cases hb : b ∈ group.getD i []
    · rw [if_pos ha, if_pos hb, if_pos ⟨ha, hb⟩]
    · rw [if_pos ha, if_neg hb, if_neg (fun hcon => hb hcon.2)]
  · by_cases hb : b ∈ group.getD i []
    · rw [if_neg ha, if_pos hb, if_neg (fun hcon => ha hcon.1)]
    · rw [if_neg ha, if_neg hb, if_neg (fun hcon => ha hcon.1)]

end ProbeM12
