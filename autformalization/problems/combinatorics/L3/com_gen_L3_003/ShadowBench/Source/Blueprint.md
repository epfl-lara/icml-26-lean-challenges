# Formalization Blueprint: `combinatorics/L3/com_gen_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet
```

## Required Names

- `contract_closure_eq_contract_delete`
- `contract_closure_eq`
- `contract_spanning_iff`

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
open Set

/-
Formalize in Lean the following named items from Text.

1. Lemma (contract_closure_eq_contract_delete)
   The lemma must be named `contract_closure_eq_contract_delete`.
   Matched text (candidate 0, lemma, label=Contracting the closure): \begin{lemma}[Contracting the closure] For any \(C\subseteq E(M)\), \[ M/\mathrm{cl}_M(C)=
                                                                     (M/C)\setminus\bigl(\mathrm{cl}_M(C)\setminus C\bigr). \] \end{lemma}
2. Lemma (contract_closure_eq)
   The lemma must be named `contract_closure_eq`.
   Matched text (candidate 1, lemma, label=Closure in a contraction): \begin{lemma}[Closure in a contraction] For any sets \(C,X\), \[
                                                                      \mathrm{cl}_{M/C}(X)=\mathrm{cl}_M(X\cup C)\setminus C. \] \end{lemma}
3. Lemma (contract_spanning_iff)
   The lemma must be named `contract_spanning_iff`.
   Matched text (candidate 2, theorem, label=contract_spanning_iff): \begin{theorem}[contract_spanning_iff] Assume \(C\subseteq E(M)\). Then \[ X \text{ is
                                                                     spanning in } M/C \;\Longleftrightarrow\; \bigl(X\cup C \text{ is spanning in } M\bigr)\
                                                                     \wedge\ \mathrm{Disjoint}(X,C). \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
