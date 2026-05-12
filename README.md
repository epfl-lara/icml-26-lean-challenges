# ICML Challenge EPFLemma Projects

These are focused working copies of `/localhome/milikic/challenges` for EPFLemma.
The original starting kit is left untouched.

Each project keeps the official `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`, narrows `Challenges.lean` to one topic, and shares the
downloaded Lake dependency tree through:

```text
.lake/packages -> /localhome/milikic/challenges/.lake/packages
```

Projects:

| Directory | EPFLemma name | Scope |
| --- | --- | --- |
| `binary_heap` | `icml-binary-heap` | Binary heap challenge files |
| `dijkstra` | `icml-dijkstra` | Dijkstra challenge files |
| `minimum_spanning_tree` | `icml-mst` | Kruskal/MST challenge |
| `segment_tree` | `icml-segment-tree` | Segment tree challenge files |
| `treap` | `icml-treap` | Treap algorithm and analysis challenge files |

From any project directory:

```bash
lake build
epflemma project show
epflemma workflow prove <challenge-file>
```

Each project has a `docs/README.md` and downloaded sources under
`docs/sources/`.
