# Formalization Blueprint: `algebra/L3/alg_gen_L3_004`

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

- `contract_inter_ground_eq`
- `contract_ground_subset_ground`
- `coindep_contract_iff`
- `Coindep.coindep_contract_of_disjoint`
- `contract_isCocircuit_iff`
- `Indep.contract_isBase_iff`
- `Indep.contract_indep_iff`
- `IsNonloop.contractElem_indep_iff`
- `Indep.union_indep_iff_contract_indep`
- `Indep.diff_indep_contract_of_subset`
- `Indep.contract_dep_iff`
- `IsBasis.contract_eq_contract_delete`

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

1. Lemma (contract_inter_ground_eq)
   The lemma must be named `contract_inter_ground_eq`.
   Matched text (candidate 0, lemma, label=Contraction): \begin{lemma}[Contraction] Let \( M \) be a matroid on a ground set \( E \), and let \( C
                                                         \subseteq E \). The \emph{contraction} of \( C \) from \( M \), denoted \( M / C \), is
                                                         defined by \[ M / C := (M^\ast \setminus C)^\ast . \] \end{lemma}
2. Lemma (contract_ground_subset_ground)
   The lemma must be named `contract_ground_subset_ground`.
   Matched text (candidate 1, lemma, label=Ground set of contraction): \begin{lemma}[Ground set of contraction] For any matroid \( M \) and set \( C \subseteq E
                                                                       \), \[ E(M / C) = E(M) \setminus C . \] \end{lemma}
3. Lemma (coindep_contract_iff)
   The lemma must be named `coindep_contract_iff`.
   Matched text (candidate 2, lemma, label=Duality of contraction and deletion): \begin{lemma}[Duality of contraction and deletion] For any matroid \( M \) and set \( X
                                                                                 \subseteq E \), \[ (M / X)^\ast = M^\ast \setminus X, \qquad (M \setminus X)^\ast = M^\ast /
                                                                                 X . \] \end{lemma}
4. Lemma (Coindep.coindep_contract_of_disjoint)
   The lemma must be named `Coindep.coindep_contract_of_disjoint`.
   Matched text (candidate 3, lemma, label=Iterated contraction): \begin{lemma}[Iterated contraction] For any matroid \( M \) and sets \( C_1, C_2 \subseteq E
                                                                  \), \[ M / C_1 / C_2 = M / (C_1 \cup C_2). \] In particular, \[ M / C_1 / C_2 = M / C_2 /
                                                                  C_1 . \] \end{lemma}
5. Lemma (contract_isCocircuit_iff)
   The lemma must be named `contract_isCocircuit_iff`.
   Matched text (candidate 4, lemma, label=Trivial contraction): \begin{lemma}[Trivial contraction] For any matroid \( M \), \[ M / \varnothing = M . \]
                                                                 \end{lemma}
6. Lemma (Indep.contract_isBase_iff)
   The lemma must be named `Indep.contract_isBase_iff`.
   Matched text (candidate 5, lemma, label=Equality of contractions): \begin{lemma}[Equality of contractions] For any matroid \( M \) and sets \( C_1, C_2
                                                                      \subseteq E \), \[ M / C_1 = M / C_2 \;\Longleftrightarrow\; C_1 \cap E(M) = C_2 \cap E(M).
                                                                      \] \end{lemma}
7. Lemma (Indep.contract_indep_iff)
   The lemma must be named `Indep.contract_indep_iff`.
   Matched text (candidate 6, lemma, label=Coindependence under contraction): \begin{lemma}[Coindependence under contraction] Let \( M \) be a matroid, \( C \subseteq
                                                                              E(M) \), and \( X \subseteq E(M) \). Then \[ X \text{ is coindependent in } M / C
                                                                              \;\Longleftrightarrow\; X \text{ is coindependent in } M \text{ and } X \cap C = \varnothing
                                                                              . \] \end{lemma}
8. Lemma (IsNonloop.contractElem_indep_iff)
   The lemma must be named `IsNonloop.contractElem_indep_iff`.
   Matched text (candidate 7, lemma, label=Cocircuits under contraction): \begin{lemma}[Cocircuits under contraction] Let \( M \) be a matroid and \( C \subseteq E(M)
                                                                          \). A set \( K \) is a cocircuit of \( M / C \) if and only if \( K \) is a cocircuit of \(
                                                                          M \) and \( K \cap C = \varnothing \). \end{lemma}
9. Lemma (Indep.union_indep_iff_contract_indep)
   The lemma must be named `Indep.union_indep_iff_contract_indep`.
   Matched text (candidate 8, lemma, label=Bases under contraction): \begin{lemma}[Bases under contraction] Let \( M \) be a matroid and let \( I \subseteq E(M)
                                                                     \) be independent. A set \( B \) is a basis of \( M / I \) if and only if \[ B \cup I \text{
                                                                     is a basis of } M \quad\text{and}\quad B \cap I = \varnothing . \] \end{lemma}
10. Lemma (Indep.diff_indep_contract_of_subset)
   The lemma must be named `Indep.diff_indep_contract_of_subset`.
   Matched text (candidate 9, lemma, label=Independence under contraction): \begin{lemma}[Independence under contraction] Let \( M \) be a matroid and let \( I
                                                                            \subseteq E(M) \) be independent. For any set \( J \subseteq E(M) \), \[ J \text{ is
                                                                            independent in } M / I \;\Longleftrightarrow\; J \cap I = \varnothing \;\text{ and }\; J
                                                                            \cup I \text{ is independent in } M . \] \end{lemma}
11. Lemma (Indep.contract_dep_iff)
   The lemma must be named `Indep.contract_dep_iff`.
   Matched text (candidate 10, lemma, label=Single-element contraction): \begin{lemma}[Single-element contraction] Let \( M \) be a matroid and let \( e \) be a non-
                                                                         loop element of \( M \). For any set \( I \), \[ I \text{ is independent in } M / \{e\}
                                                                         \;\Longleftrightarrow\; e \notin I \;\text{ and }\; I \cup \{e\} \text{ is independent in }
                                                                         M . \] \end{lemma}
12. Lemma (IsBasis.contract_eq_contract_delete)
   The lemma must be named `IsBasis.contract_eq_contract_delete`.
   Matched text (candidate 11, theorem, label=IsBasis.contract_eq_contract_delete): \begin{theorem}[IsBasis.contract_eq_contract_delete] Let \( M \) be a matroid, \( X
                                                                                    \subseteq E(M) \), and let \( I \) be a basis of \( X \). Then \[ M / X = M / I \setminus (X
                                                                                    \setminus I). \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
