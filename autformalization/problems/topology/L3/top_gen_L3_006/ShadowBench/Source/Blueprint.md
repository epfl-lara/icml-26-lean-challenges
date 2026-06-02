# Formalization Blueprint: `topology/L3/top_gen_L3_006`

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
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
```

## Required Names

- `existsUnique_continuousMap_lifts`

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
Formalize in Lean the Theorem (existsUnique_continuousMap_lifts) from Text.

The theorem must be named `existsUnique_continuousMap_lifts`.
   Matched text (candidate 0, theorem, label=existsUnique_continuousMap_lifts): \begin{theorem}[existsUnique_continuousMap_lifts] Let \(p:E\to X\) be a local homeomorphism.
                                                                                Let \(A\) be a path-connected and locally path-connected topological space. Let \[ f:A\to X
                                                                                \] be a continuous map, and fix points \(a_0\in A\) and \(e_0\in E\) such that \[
                                                                                p(e_0)=f(a_0). \] Assume the following two conditions. \begin{enumerate} \item For every
                                                                                path \(\gamma:I\to A\) with \(\gamma(0)=a_0\), there exists a p…
-/
```
