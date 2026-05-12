# Binary Heap References

Challenge files:

- `Challenges/BinaryHeap_Dijkstra/Challenge_BinaryHeap_1.lean`
- `Challenges/BinaryHeap_Dijkstra/Challenge_BinaryHeap_2.lean`
- `Challenges/BinaryHeap_Dijkstra/Challenge_BinaryHeap_3.lean`
- `Challenges/BinaryHeap_Dijkstra/Challenge_BinaryHeap_4.lean`

Local source pack:

- `sources/cmu-priority-queues-and-heaps.html`
  - URL: https://web2.qatar.cmu.edu/cs/15121/notes/heaps/
  - Useful for min-heap invariants, extract-min/delete-min, insert, and heapify intuition.
- `sources/functional-approach-standard-binary-heaps-arxiv-1312.4666.pdf`
  - URL: https://arxiv.org/abs/1312.4666
  - Useful because the Lean definitions are tree-shaped, not array-shaped; this paper discusses binary heaps from a functional perspective.

Lean entry points:

- Start in `Challenges/BinaryHeap_Dijkstra/Def_BinaryHeap.lean`.
- The key predicates and functions are `is_min_heap`, `heap_min`, `heapify`, `extract_min`, `insert`, and `decrease_priority`.
- File-scoped EPFLemma runs are usually best here because all four binary heap challenges are independent.
