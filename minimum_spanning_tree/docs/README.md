# Minimum Spanning Tree References

Challenge file:

- `Challenges/Minimum_Spanning_Tree/Challenge_Kruskal.lean`

Local source pack:

- `sources/kruskal-1956-shortest-spanning-subtree.pdf`
  - URL: https://www.ams.org/journals/proc/1956-007-01/S0002-9939-1956-0078686-7/S0002-9939-1956-0078686-7.pdf
  - Original Kruskal paper.
- `sources/duke-mst-cut-cycle-kruskal-notes.pdf`
  - URL: https://courses.cs.duke.edu/spring17/compsci330/Notes/MST.pdf
  - Useful for cut property, cycle property, and exchange arguments.
- `sources/ksu-kruskal.html`
  - URL: https://textbooks.cs.ksu.edu/cc315/iii-graphs/9-graphs--minimum-spanning-trees/3-kruskal/
  - Useful implementation-level Kruskal overview.

Lean entry points:

- Start in `Challenges/Minimum_Spanning_Tree/Challenge_Kruskal.lean`.
- Definitions are split across `Def_ArrayN.lean`, `Def_ForestN.lean`,
  `Def_UnionFindN.lean`, and `Def_WeightedGraph.lean`.
- Expect the proof to follow an exchange/cut-property argument plus facts about
  the union-find forest state.
