import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

namespace Splay

/-- (50 pts) Sequential access on a splay tree. Prove that splaying the
access sequence `1, 2, ..., n` on any BST of `n` nodes containing those
keys takes total cost at most `c * n` for some constant `c`. The constant
`c` is the metric used for the Phase 2 tie break: among submissions
solving this problem, a smaller constant wins. -/
theorem sequential : ∃ c, ∀ n, let X := one_to_n n
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) →
    IsBST init → (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n := sorry

end Splay
