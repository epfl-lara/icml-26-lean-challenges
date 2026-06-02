# Formalization Blueprint: `combinatorics/L3/com_gen_L3_002`

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
import Mathlib.Combinatorics.Matroid.Minor.Contract
```

## Required Names

- `IsMinor`
- `IsStrictMinor`
- `IsMinor.exists_eq_contract_delete_disjoint`
- `IsMinor_antisymm`

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

1. Definition (IsMinor)
   The definition must be named `IsMinor`.
   Matched text (candidate 0, definition, label=IsMinor): \begin{definition}[IsMinor] A matroid $N$ is a \emph{minor} of a matroid $M$ if there exist
                                                          subsets $C,D\subseteq \alpha$ such that \[ N = M / C \setminus D. \] We write $N \le_m M$ to
                                                          denote that $N$ is a minor of $M$. \end{definition}
2. Definition (IsStrictMinor)
   The definition must be named `IsStrictMinor`.
   Matched text (candidate 1, definition, label=IsStrictMinor): \begin{definition}[IsStrictMinor] A matroid $N$ is a \emph{strict minor} of $M$ if $N$ is a
                                                                minor of $M$ but $M$ is not a minor of $N$. We write $N <_m M$. \end{definition}
3. Lemma (IsMinor.exists_eq_contract_delete_disjoint)
   The lemma must be named `IsMinor.exists_eq_contract_delete_disjoint`.
   Matched text (candidate 2, lemma, label=IsMinor.exists_eq_contract_delete_disjoint): \begin{lemma}[IsMinor.exists_eq_contract_delete_disjoint]\label{lem:disjoint-contract-delete}
                                                                                        If $N \le_m M$, then there exist subsets $C,D\subseteq E(M)$ such that \[ C\cap
                                                                                        D=\varnothing \qquad\text{and}\qquad N = M / C \setminus D. \] \end{lemma}
4. Lemma (IsMinor_antisymm)
   The lemma must be named `IsMinor_antisymm`.
   Matched text (candidate 3, lemma, label=IsMinor_antisymm): \begin{lemma}[IsMinor_antisymm]\label{thm:minor-order} The minor relation $\le_m$ defines a
                                                              partial order on the class of matroids on $\alpha$. Explicitly: \begin{itemize} \item $N
                                                              \le_m N$ for all $N$ (reflexivity), \item if $N \le_m M$ and $M \le_m P$, then $N \le_m P$
                                                              (transitivity), \item if $N \le_m M$ and $M \le_m N$, then $N = M$ (antisymmetry).
                                                              \end{itemize} \end{lemma}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
