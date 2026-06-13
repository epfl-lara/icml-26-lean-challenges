import Challenges.Splay_Tree.Def_Splay

namespace Splay

example (t : BinaryTree) : t.num_nodes ≤ t.num_nodes := by
  induction hN : t.num_nodes using Nat.strong_induction_on generalizing t with
  | h n ih =>
      exact le_rfl

example (t : BinaryTree) :
    ∀ u : BinaryTree, u.num_nodes < t.num_nodes → u.num_nodes ≤ u.num_nodes := by
  intro u hu
  induction hN : t.num_nodes using Nat.strong_induction_on generalizing t u with
  | h n ih =>
      exact le_rfl

example (t : BinaryTree) :
    True := by
  induction hN : t.num_nodes using Nat.strong_induction_on generalizing t with
  | h n ih =>
      cases t with
      | empty => trivial
      | node l k r =>
          have hlt : l.num_nodes < n := by
            rw [← hN]
            simp [BinaryTree.num_nodes]
            omega
          have hrec := ih l.num_nodes hlt l
          trivial

end Splay
