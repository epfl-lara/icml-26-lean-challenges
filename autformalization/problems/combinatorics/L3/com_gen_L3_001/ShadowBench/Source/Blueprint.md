# Formalization Blueprint: `combinatorics/L3/com_gen_L3_001`

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
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet
```

## Required Names

- `contract`
- `contract_ground`
- `dual_delete_dual`
- `contract_contract`
- `contract_empty`
- `contract_eq_contract_iff`
- `coindep_contract_iff`
- `contract_isCocircuit_iff`
- `Indep.contract_isBase_iff`
- `Indep.contract_indep_iff`
- `IsNonloop.contractElem_indep_iff`
- `IsBasis.contract_eq_contract_delete`

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
open Set

/-
Formalize in Lean the following named items from Text.

1. Definition (contract)
   The definition must be named `contract`.
   Matched text (candidate 0, definition, label=contract_inter_ground_eq): \begin{definition}[contract_inter_ground_eq] Let \( M \) be a matroid on a ground set \( E
                                                                           \), and let \( C \subseteq E \). The \emph{contraction} of \( C \) from \( M \), denoted \(
                                                                           M / C \), is defined by \[ M / C := (M^\ast \setminus C)^\ast . \] \end{definition}
2. Lemma (contract_ground)
   The lemma must be named `contract_ground`.
   Matched text (candidate 1, lemma, label=contract_ground_subset_ground): \begin{lemma}[contract_ground_subset_ground] For any matroid \( M \) and set \( C \subseteq
                                                                           E \), \[ E(M / C) = E(M) \setminus C . \] \end{lemma}
3. Lemma (dual_delete_dual)
   The lemma must be named `dual_delete_dual`.
   Matched text (candidate 2, lemma, label=coindep_contract_iff): \begin{lemma}[coindep_contract_iff] For any matroid \( M \) and set \( X \subseteq E \), \[
                                                                  (M / X)^\ast = M^\ast \setminus X, \qquad (M \setminus X)^\ast = M^\ast / X . \] \end{lemma}
4. Lemma (contract_contract)
   The lemma must be named `contract_contract`.
   Matched text (candidate 3, lemma, label=Coindep.coindep_contract_of_disjoint): \begin{lemma}[Coindep.coindep_contract_of_disjoint] For any matroid \( M \) and sets \( C_1,
                                                                                  C_2 \subseteq E \), \[ M / C_1 / C_2 = M / (C_1 \cup C_2). \] In particular, \[ M / C_1 /
                                                                                  C_2 = M / C_2 / C_1 . \] \end{lemma}
5. Lemma (contract_empty)
   The lemma must be named `contract_empty`.
   Matched text (candidate 4, lemma, label=contract_isCocircuit_iff): \begin{lemma}[contract_isCocircuit_iff] For any matroid \( M \), \[ M / \varnothing = M . \]
                                                                      \end{lemma}
6. Lemma (contract_eq_contract_iff)
   The lemma must be named `contract_eq_contract_iff`.
   Matched text (candidate 5, lemma, label=Indep.contract_isBase_iff): \begin{lemma}[Indep.contract_isBase_iff] For any matroid \( M \) and sets \( C_1, C_2
                                                                       \subseteq E \), \[ M / C_1 = M / C_2 \;\Longleftrightarrow\; C_1 \cap E(M) = C_2 \cap E(M).
                                                                       \] \end{lemma}
7. Lemma (coindep_contract_iff)
   The lemma must be named `coindep_contract_iff`.
   Matched text (candidate 6, lemma, label=Indep.contract_indep_iff): \begin{lemma}[Indep.contract_indep_iff] Let \( M \) be a matroid, \( C \subseteq E(M) \),
                                                                      and \( X \subseteq E(M) \). Then \[ X \text{ is coindependent in } M / C
                                                                      \;\Longleftrightarrow\; X \text{ is coindependent in } M \text{ and } X \cap C = \varnothing
                                                                      . \] \end{lemma}
8. Lemma (contract_isCocircuit_iff)
   The lemma must be named `contract_isCocircuit_iff`.
   Matched text (candidate 7, lemma, label=IsNonloop.contractElem_indep_iff): \begin{lemma}[IsNonloop.contractElem_indep_iff] Let \( M \) be a matroid and \( C \subseteq
                                                                              E(M) \). A set \( K \) is a cocircuit of \( M / C \) if and only if \( K \) is a cocircuit
                                                                              of \( M \) and \( K \cap C = \varnothing \). \end{lemma}
9. Lemma (Indep.contract_isBase_iff)
   The lemma must be named `Indep.contract_isBase_iff`.
   Matched text (candidate 8, lemma, label=Indep.union_indep_iff_contract_indep): \begin{lemma}[Indep.union_indep_iff_contract_indep] Let \( M \) be a matroid and let \( I
                                                                                  \subseteq E(M) \) be independent. A set \( B \) is a basis of \( M / I \) if and only if \[
                                                                                  B \cup I \text{ is a basis of } M \quad\text{and}\quad B \cap I = \varnothing . \]
                                                                                  \end{lemma}
10. Lemma (Indep.contract_indep_iff)
   The lemma must be named `Indep.contract_indep_iff`.
   Matched text (candidate 9, lemma, label=Indep.diff_indep_contract_of_subset): \begin{lemma}[Indep.diff_indep_contract_of_subset] Let \( M \) be a matroid and let \( I
                                                                                 \subseteq E(M) \) be independent. For any set \( J \subseteq E(M) \), \[ J \text{ is
                                                                                 independent in } M / I \;\Longleftrightarrow\; J \cap I = \varnothing \;\text{ and }\; J
                                                                                 \cup I \text{ is independent in } M . \] \end{lemma}
11. Lemma (IsNonloop.contractElem_indep_iff)
   The lemma must be named `IsNonloop.contractElem_indep_iff`.
   Matched text (candidate 10, lemma, label=Indep.contract_dep_iff): \begin{lemma}[Indep.contract_dep_iff] Let \( M \) be a matroid and let \( e \) be a non-loop
                                                                     element of \( M \). For any set \( I \), \[ I \text{ is independent in } M / \{e\}
                                                                     \;\Longleftrightarrow\; e \notin I \;\text{ and }\; I \cup \{e\} \text{ is independent in }
                                                                     M . \] \end{lemma}
12. Lemma (IsBasis.contract_eq_contract_delete)
   The lemma must be named `IsBasis.contract_eq_contract_delete`.
   Matched text (candidate 11, lemma, label=IsBasis.contract_eq_contract_delete): \begin{lemma}[IsBasis.contract_eq_contract_delete] Let \( M \) be a matroid, \( X \subseteq
                                                                                  E(M) \), and let \( I \) be a basis of \( X \). Then \[ M / X = M / I \setminus (X \setminus
                                                                                  I). \] \end{lemma}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
