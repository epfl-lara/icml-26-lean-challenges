import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

namespace Splay

/-- (200 pts) The Traversal Conjecture: a long standing open problem in
dynamic data structures, due to Sleator and Tarjan. Closely related to
(but distinct from) the Deque Conjecture: the Deque Conjecture asks
the same `c * n` bound for sequences avoiding both `213` and `231`,
whereas this Traversal Conjecture only requires avoidance of `231`. The
traversal sequences (BST preorder, postorder, etc.) all fall in the
`231`-avoiding class, hence the name.

Prove that splaying any access sequence that avoids the pattern `231`
takes total cost at most `c * n` for some constant `c`. A successful
resolution of this conjecture would be a major theoretical result in
its own right. -/
theorem traversal_conjecture : ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n := sorry

end Splay
