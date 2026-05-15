# Formalization Blueprint: `combinatorics/L3/com_gen_L3_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
```

## Required Names

- `isBipartiteWith_sum_degrees_eq_twice_card_edges`
- `isBipartiteWith_sum_degrees_eq_card_edges`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open BigOperators Finset Fintype

/-
Formalize in Lean the following named items from Text.

1. Lemma (isBipartiteWith_sum_degrees_eq_twice_card_edges)
   The lemma must be named `isBipartiteWith_sum_degrees_eq_twice_card_edges`.
   Matched text (candidate 0, theorem, label=Bipartite with respect to two sets): \begin{theorem}[Bipartite with respect to two sets] Let \(G\) be a simple graph on a vertex
                                                                                  set \(V\), and let \(s,t \subseteq V\). We say that \(G\) is \emph{bipartite with respect to
                                                                                  \(s\) and \(t\)} if: \begin{enumerate} \item \(s\) and \(t\) are disjoint, and \item every
                                                                                  edge of \(G\) connects a vertex in \(s\) to a vertex in \(t\) (in one direction or the
                                                                                  other). \end{enumerate} \end{theorem}
2. Theorem (isBipartiteWith_sum_degrees_eq_card_edges)
   The theorem must be named `isBipartiteWith_sum_degrees_eq_card_edges`.
   Matched text (candidate 1, theorem, label=isBipartiteWith_sum_degrees_eq_card_edges): \begin{theorem}[isBipartiteWith_sum_degrees_eq_card_edges] Let \(G\) be a finite simple
                                                                                         graph, and let \(s,t \subseteq V\) be a bipartition of \(G\) in the above sense. Then \[
                                                                                         \sum_{v \in s} \deg_G(v) \;=\; |E(G)|. \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
