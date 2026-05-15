# Formalization Blueprint: `topology/L3/top_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton
```

## Required Names

- `homotopyTo`
- `homotopyTo_apply`
- `homotopicTo`

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
open scoped unitInterval Topology
open Homeomorph

/-
Formalize in Lean the following named items from Text.

1. Definition (homotopyTo)
   The definition must be named `homotopyTo`.
   Matched text (candidate 0, theorem): \begin{theorem} Let $X$ be a topological space, let $x \in X$, and let $N$ be a finite index
                                        set. Fix an index $i \in N$, and write $N \setminus i := N \setminus \{i\}$. Let \[ \Psi_i :
                                        I \times I^{N\setminus i} \xrightarrow{\cong} I^N \] denote the canonical homeomorphism that
                                        inserts the coordinate $t \in I$ in the $i$-th position. For a generalized $N$-loop \[ p \in
                                        \Omega^{N}(X,x), \qquad p : I^N \to X, \] defin…
2. Theorem (homotopyTo_apply)
   The theorem must be named `homotopyTo_apply`.
   Matched text (candidate 1, lemma): \begin{lemma} We have a well-defined map \[ \mathrm{toLoop}_i : \Omega^{N}(X,x)
                                      \longrightarrow \Omega\bigl(\Omega^{N\setminus i}(X,x),\,\mathrm{const}\bigr), \] sending an
                                      $N$-dimensional generalized loop to a loop of generalized $(N\setminus i)$-loops based at
                                      the constant loop. \end{lemma}
3. Theorem (homotopicTo)
   The theorem must be named `homotopicTo`.
   Matched text (candidate 2, theorem, label=homotopicTo): \begin{theorem}[homotopicTo] Let $X$ be a topological space, $x\in X$, and $N$ an index set.
                                                           Fix $i\in N$. Let \[ p,q \in \Omega^{N}(X,x). \] Assume that the associated paths \[
                                                           \mathrm{toLoop}_i(p),\ \mathrm{toLoop}_i(q) : I \longrightarrow
                                                           \Omega^{N\setminus\{i\}}(X,x) \] are homotopic relative to endpoints. Then $p$ and $q$ are
                                                           homotopic relative to the boundary $\partial I^{N}$. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
