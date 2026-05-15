# Formalization Blueprint: `topology/L2/top_gen_L2_019`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Perfect
```

## Required Names

- `isTotallyDisconnected_cantorSet`

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
open Set Topology

/-
Formalize in Lean the Theorem (isTotallyDisconnected_cantorSet) from Text.

The theorem must be named `isTotallyDisconnected_cantorSet`.
   Matched text (candidate 0, theorem, label=isTotallyDisconnected_cantorSet): \begin{theorem}[isTotallyDisconnected_cantorSet] Prove that the Cantor set $\mathcal{C}$ is
                                                                               totally disconnected and perfect. \end{theorem}
-/
```
