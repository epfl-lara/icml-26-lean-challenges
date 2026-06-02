# Formalization Blueprint: `topology/L3/top_gen_L3_008`

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
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
```

## Required Names

- `existsUnique_continuousMap_lifts_of_range_le`

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
Formalize in Lean the Theorem (existsUnique_continuousMap_lifts_of_range_le) from Text.

The theorem must be named `existsUnique_continuousMap_lifts_of_range_le`.
   Matched text (candidate 0, theorem, label=existsUnique_continuousMap_lifts_of_range_le): \begin{theorem}[existsUnique_continuousMap_lifts_of_range_le] Let \(p : E \to X\) be a
                                                                                            covering map, let \(A\) be path connected and locally path connected, and let \[ f : A \to X
                                                                                            \] be continuous. Fix points \(a_0 \in A\) and \(e_0 \in E\) such that \[ p(e_0)=f(a_0). \]
                                                                                            Assume that \[ f_*\bigl(\pi_1(A,a_0)\bigr)\subseteq p_*\bigl(\pi_1(E,e_0)\bigr) \subseteq
                                                                                            \pi_1(X,f(a_0)). \] Then there exists a unique continuous…
-/
```
