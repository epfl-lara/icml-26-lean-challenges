# Treap References

Challenge files:

- `Challenges/Treap/Challenge_Analysis_1.lean`
- `Challenges/Treap/Challenge_Analysis_2.lean`
- `Challenges/Treap/Challenge_Treap_1.lean` through `Challenge_Treap_15.lean`

Local source pack:

- `sources/seidel-aragon-randomized-search-trees-1996.pdf`
  - URL: https://faculty.washington.edu/aragon/pubs/rst96.pdf
  - Core treap/randomized search tree paper; useful for split/join and expected depth.
- `sources/cmu-treaps-notes.pdf`
  - URL: https://www.cs.cmu.edu/~15210/notes/treaps.pdf
  - Useful for treap invariants, split, merge, and randomized analysis.
- `sources/martinez-roura-randomized-binary-search-trees-1998.pdf`
  - URL: https://www.cs.upc.edu/~conrado/research/papers/jacm-mr98.pdf
  - Useful supplementary randomized BST analysis.

Lean entry points:

- Algorithm proofs start in `Challenges/Treap/Def_Treap.lean`.
- Composite operation proofs use `Challenges/Treap/Def_TreapComposite.lean`;
  `Challenge_Treap_7` through `_9` depend on earlier split/merge lemmas.
- TimeM challenges `_10` through `_15` only need `Def_Treap.lean`.
- Analysis proofs start in `Challenges/Treap/Def_Analysis.lean`; prove
  `Challenge_Analysis_1` before `Challenge_Analysis_2`.
