import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

namespace Splay

/-- (100 pts) The Deque Conjecture: a long standing open problem in
dynamic data structures, due to Sleator and Tarjan. Strengthens the
regular Splay deque challenge (which proves a `c * n * α(n)` bound) by
asking for the tighter `c * n` bound on the same input class, namely
sequences that avoid both `213` and `231`. A successful resolution
would be a major theoretical result in its own right. -/
theorem deque_conjecture : ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n := sorry

end Splay
