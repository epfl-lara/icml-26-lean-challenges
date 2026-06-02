import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

namespace Splay

/-- (50 pts) Deque access on a splay tree. Prove that splaying any
deque-like access sequence (one that avoids the patterns `213` and `231`)
on a BST of `n` nodes takes total cost at most `c * n * α(n)` for some
constant `c`, where `α` is Klazar's Ackermann inverse. The constant `c`
is the metric used for the Phase 2 tie break: among submissions solving
this problem, a smaller constant wins. -/
theorem deque : ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n * (KlazarAckermann.alpha n) := sorry

end Splay
