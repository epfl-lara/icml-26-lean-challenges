# Formalization Blueprint: `topology/L3/top_gen_L3_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
```

## Required Names

- `exists_path_lifts`
- `eq_liftPath_iff`
- `eq_liftPath_iff'`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open Topology unitInterval

/-
Formalize in Lean the following named items from Text.

1. Theorem (exists_path_lifts)
   The theorem must be named `exists_path_lifts`.
   Matched text (candidate 0, theorem, label=Existence of a path lifting): \begin{theorem}[Existence of a path lifting] Let \[ p:E\to X \] be a covering map. Let \[
                                                                           \gamma:I\to X \] be a path, and let \(e\in E\) be such that \[ \gamma(0)=p(e). \] Then there
                                                                           exists a path \[ \Gamma:I\to E \] such that \[ p\circ \Gamma=\gamma \qquad\text{and}\qquad
                                                                           \Gamma(0)=e. \] \end{theorem}
2. Lemma (eq_liftPath_iff)
   The lemma must be named `eq_liftPath_iff`.
   Matched text (candidate 1, lemma, label=Uniqueness of lifts): \begin{lemma}[Uniqueness of lifts] Let \[ f:E\to X \] be a covering map, and let \(A\) be a
                                                                 preconnected topological space. Suppose \[ g_1,g_2:A\to E \] are continuous maps such that
                                                                 \[ f\circ g_1=f\circ g_2. \] If there exists a point \(a\in A\) such that \[ g_1(a)=g_2(a),
                                                                 \] then \[ g_1=g_2. \] \end{lemma}
3. Lemma (eq_liftPath_iff')
   The lemma must be named `eq_liftPath_iff'`.
   Matched text (candidate 2, theorem, label=eq_liftPath_iff'): \begin{theorem}[eq_liftPath_iff'] Let \[ p:E\to X \] be a covering map, let \[ \gamma:I\to X
                                                                \] be a path, and let \(e\in E\) satisfy \[ \gamma(0)=p(e). \] Let \[
                                                                \widetilde{\gamma}:I\to E \] be the chosen lift of \(\gamma\) starting at \(e\), so that \[
                                                                p\circ \widetilde{\gamma}=\gamma \qquad\text{and}\qquad \widetilde{\gamma}(0)=e. \] Then for
                                                                any map \(\Gamma:I\to E\), \[ \Gamma=\widetilde{\gamma} \] if and only…

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
