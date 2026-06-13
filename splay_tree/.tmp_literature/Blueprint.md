# Source-Backed Direct Proof Track For `Splay.traversal_conjecture`

## Sources

- Levy-Tarjan, "Splaying Preorders and Postorders", arXiv:1907.06309.
  - Theorem 2: insertion-splaying a preorder takes linear time.
  - Lemma 3: for a 231-avoiding preorder, the next touched node is the smallest sub-root.
  - Potential: twice the number of touched nodes that are ancestors of sub-roots.
- Chalermsook-Goswami-Kozma-Mehlhorn-Saranurak, "Pattern-avoiding access in binary search trees", arXiv:1507.06953.
  - Records the arbitrary-initial splay traversal conjecture as unresolved.
  - Notes the path-preorder special case as a barrier for traversal/deque/split.
- Chaudhuri-Höft, "Splaying a search tree in preorder takes linear time".
  - Earlier special case: the initial tree is the same tree whose preorder is accessed.
  - Levy-Tarjan cite this result and replace it with a cleaner insertion-splaying proof.

## Lean Target

The challenge theorem is stronger than Levy-Tarjan Theorem 2:

- Lean allows arbitrary initial BST, not only the insertion tree of the preorder.
- Lean allows repeated keys in a length-`n` access function `Fin n -> Nat`.
- The constant must be global: `∃ c, ∀ n X init, ...`.

Therefore the direct proof must contain an explicit arbitrary-initial lift. It cannot be imported from the literature.

## Planned Declarations

- `insertionTreeOfSeq`: BST obtained by first occurrence insertion order.
- `TouchedState`: current splay tree plus a decidable touched set.
- `subRoot`: untouched node with touched parent.
- `preorder_next_is_smallest_subRoot`: formal Levy-Tarjan Lemma 3 for 231-avoiding sequences, with repeated-key normalization.
- `preorder_subRoot_leftDepth_le_one`: invariant in Levy-Tarjan Theorem 2.
- `preorder_insertion_amortized_step_le_six`: potential-step theorem for zig-zig/zig-zag/zig cases.
- `preorder_insertion_splayPathSum_le_const`: insertion-tree bound.
- `arbitrary_initial_lift_from_insertion_tree`: new theorem needed to close this challenge:
  transfer the touched/sub-root potential from the insertion tree to an arbitrary initial BST with the same key set.

## Current Fidelity Check

`preorder_insertion_splayPathSum_le_const` is source-backed by Levy-Tarjan.
`arbitrary_initial_lift_from_insertion_tree` is not source-backed; it is the exact open gap identified by Chalermsook et al. for splay.
