# ShadowBench Instructions: `combinatorics/L3/com_gen_L3_005`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
```

## Expected Declaration Names

- `IsBipartiteWith`
- `isBipartiteWith_sum_degrees_eq_card_edges`

## Formalization Rules

```text
open BigOperators Finset Fintype

/-
Formalize in Lean the following named items from Text.

1. Definition (IsBipartiteWith)
   The definition must be named `IsBipartiteWith`.
   Matched text (candidate 0, definition, label=isBipartiteWith_sum_degrees_eq_twice_card_edges): \begin{definition}[isBipartiteWith_sum_degrees_eq_twice_card_edges] Let \(G\) be a simple
                                                                                                  graph on a vertex set \(V\), and let \(s,t \subseteq V\). We say that \(G\) is
                                                                                                  \emph{bipartite with respect to \(s\) and \(t\)} if: \begin{enumerate} \item \(s\) and \(t\)
                                                                                                  are disjoint, and \item every edge of \(G\) connects a vertex in \(s\) to a vertex in \(t\)
                                                                                                  (in one direction or the other). \end{enumerate} \end{definition}
2. Theorem (isBipartiteWith_sum_degrees_eq_card_edges)
   The theorem must be named `isBipartiteWith_sum_degrees_eq_card_edges`.
   Matched text (candidate 1, theorem, label=isBipartiteWith_sum_degrees_eq_card_edges): \begin{theorem}[isBipartiteWith_sum_degrees_eq_card_edges] Let \(G\) be a finite simple
                                                                                         graph, and let \(s,t \subseteq V\) be a bipartition of \(G\) in the above sense. Then \[
                                                                                         \sum_{v \in s} \deg_G(v) \;=\; |E(G)|. \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
