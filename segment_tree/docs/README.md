# Segment Tree References

Challenge files:

- `Challenges/Segment_Tree/Challenge_Build.lean`
- `Challenges/Segment_Tree/Challenge_CoverageIntervalDefs.lean`
- `Challenges/Segment_Tree/Challenge_Query_1.lean`
- `Challenges/Segment_Tree/Challenge_Query_2.lean`

Local source pack:

- `sources/cp-algorithms-segment-tree.html`
  - URL: https://cp-algorithms.com/data_structures/segment_tree.html
  - Useful for build/query decomposition and range aggregation intuition.
- `sources/erickson-range-and-segment-trees.pdf`
  - URL: https://jeffe.cs.illinois.edu/teaching/225H/notes/range-segment.pdf
  - Useful for interval decomposition and tree coverage ideas.
- `sources/cornell-segment-trees.pdf`
  - URL: https://www.cs.cornell.edu/courses/cs5199/2019fa/resource/SegmentTrees.pdf
  - Useful for query complexity and range splitting.

Lean entry points:

- Start in `Challenges/Segment_Tree/Def_SegmentTree.lean`.
- `Challenge_CoverageIntervalDefs.lean` feeds `Def_Query.lean`; solve or inspect it before query proofs.
- `Challenge_Build.lean` is an implementation target, while `Challenge_Query_1.lean`
  and `Challenge_Query_2.lean` are correctness and time-bound proof targets.
