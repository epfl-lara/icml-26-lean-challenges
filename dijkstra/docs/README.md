# Dijkstra References

Challenge files:

- `Challenges/BinaryHeap_Dijkstra/Challenge_Dijkstra_1.lean`
- `Challenges/BinaryHeap_Dijkstra/Challenge_Dijkstra_2.lean`
- `Challenges/BinaryHeap_Dijkstra/Challenge_Dijkstra_3.lean`

Local source pack:

- `sources/dijkstra-1959-two-problems.pdf`
  - URL: https://www.cs.yale.edu/homes/lans/readings/routing/dijkstra-routing-1959.pdf
  - Original Dijkstra paper; useful for the invariant shape behind shortest-path correctness.
- `sources/generic-dijkstra-correctness-arxiv-2204.13547.pdf`
  - URL: https://arxiv.org/abs/2204.13547
  - Useful for a modern correctness proof structure and monotonicity/invariant phrasing.

Lean entry points:

- Start in `Challenges/BinaryHeap_Dijkstra/Def_Dijkstra.lean`.
- The proof chain is real: `Challenge_Dijkstra_1` feeds `Def_BinaryHeapComposite`,
  `Challenge_Dijkstra_2` feeds `Def_DijkstraComposite`, and `Challenge_Dijkstra_3`
  is the final correctness statement.
- Work in dependency order: `Challenge_Dijkstra_1`, then `_2`, then `_3`.
