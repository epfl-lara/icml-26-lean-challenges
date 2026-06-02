# Formalization Blueprint: `topology/L2/top_gen_L2_006`

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
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.UnitInterval
```

## Required Names

- `monodromy_theorem`

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
Formalize in Lean the Theorem (monodromy_theorem) from Text.

The theorem must be named `monodromy_theorem`.
   Matched text (candidate 0, theorem, label=monodromy_theorem): \begin{theorem}[monodromy_theorem] Let $\gamma_0,\gamma_1:I\to X$ be paths and let
                                                                 $\gamma:I\times I\to X$ be a homotopy rel.\ endpoints between them. Let $\Gamma:I\to C(I,E)$
                                                                 be a family of continuous paths in $E$ such that \[ p(\Gamma(t)(s))=\gamma(t,s)\quad \forall
                                                                 t,s\in I, \qquad \Gamma(t)(0)=\Gamma(0)(0)\quad \forall t\in I. \] Then
                                                                 $\Gamma(t)(1)=\Gamma(0)(1)$ for all $t\in I$. \end{theorem}
-/
```
