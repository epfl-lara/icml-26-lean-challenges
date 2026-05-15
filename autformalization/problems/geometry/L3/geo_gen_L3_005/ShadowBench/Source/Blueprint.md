# Formalization Blueprint: `geometry/L3/geo_gen_L3_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.VectorBundle.Basic
```

## Required Names

- `proj_homotopyEquiv`

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
open Bundle ContinuousMap Topology

/-
Formalize in Lean the Definition (proj_homotopyEquiv) from Text.

The definition must be named `proj_homotopyEquiv`.
   Matched text (candidate 0, definition, label=proj_homotopyEquiv): \begin{definition}[proj_homotopyEquiv] Let $E$ be a vector bundle over a topological space
                                                                     $M$. Show that the projection map $\pi : E \to M$ is a homotopy equivalence.
                                                                     \end{definition}
-/
```
