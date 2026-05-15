# Formalization Blueprint: `combinatorics/L3/com_gen_L3_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Copy
```

## Required Names

- `IsExtremal.prop`
- `exists_isExtremal_iff_exists`

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
open Finset Fintype

/-
Formalize in Lean the following named items from Text.

1. Lemma (IsExtremal.prop)
   The lemma must be named `IsExtremal.prop`.
   Matched text (candidate 0, theorem, label=Extremal graph): \begin{theorem}[Extremal graph] Let \(V\) be a finite vertex set, and let \(p\) be a
                                                              property of simple graphs on \(V\). A simple graph \(G\) on \(V\) is called \emph{extremal
                                                              with respect to \(p\)} if \[ p(G) \quad\text{and}\quad \text{for every simple graph } G'
                                                              \text{ on } V \text{ with } p(G'), \; |E(G')| \le |E(G)|. \] \end{theorem}
2. Theorem (exists_isExtremal_iff_exists)
   The theorem must be named `exists_isExtremal_iff_exists`.
   Matched text (candidate 1, theorem, label=exists_isExtremal_iff_exists): \begin{theorem}[exists_isExtremal_iff_exists] Let \(V\) be a finite vertex set, and let
                                                                            \(p\) be a property of simple graphs on \(V\). Then the following are equivalent: \[
                                                                            \exists\, G \text{ on } V \text{ such that } p(G) \quad\Longleftrightarrow\quad \exists\, G
                                                                            \text{ on } V \text{ that is extremal with respect to } p. \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
