# Formalization Blueprint: `topology/L3/top_gen_L3_004`

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

- `exists_lift_nhds`

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
Formalize in Lean the Theorem (exists_lift_nhds) from Text.

The theorem must be named `exists_lift_nhds`.
   Matched text (candidate 0, theorem, label=exists_lift_nhds): \begin{theorem}[exists_lift_nhds] Let \(p : E \to X\) be a local homeomorphism. Denote the
                                                                unit interval \([0,1]\) by \(I\). Suppose \(f:I \times A \to X\) is a continuous map and \(g
                                                                : I \times A \to E\) is a lift of \(f\) continuous on \(\{0\} \times A \cup I \times \{a\}\)
                                                                for some $a \in A$. Then there exists a neighborhood \(N\) of \(a\) and \(g':I \times A \to
                                                                E\) continuous on \(I \times N\) that agrees with…
-/
```
