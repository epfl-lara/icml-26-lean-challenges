# Formalization Blueprint: `combinatorics/L3/com_gen_L3_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Combinatorics.Matroid.Minor.Contract
```

## Required Names

- `IsMinor.refl`
- `IsMinor.trans`
- `IsMinor.eq_of_ground_subset`
- `IsMinor.antisymm`

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

1. Lemma (IsMinor.refl)
   The lemma must be named `IsMinor.refl`.
   Matched text (candidate 0, lemma, label=Minor): \begin{lemma}[Minor] A matroid $N$ is a \emph{minor} of a matroid $M$ if there exist subsets
                                                   $C,D\subseteq \alpha$ such that \[ N = M / C \setminus D. \] We write $N \le_m M$ to denote
                                                   that $N$ is a minor of $M$. \end{lemma}
2. Lemma (IsMinor.trans)
   The lemma must be named `IsMinor.trans`.
   Matched text (candidate 1, definition, label=Strict minor): \begin{definition}[Strict minor] A matroid $N$ is a \emph{strict minor} of $M$ if $N$ is a
                                                               minor of $M$ but $M$ is not a minor of $N$. We write $N <_m M$. \end{definition}
3. Lemma (IsMinor.eq_of_ground_subset)
   The lemma must be named `IsMinor.eq_of_ground_subset`.
   Matched text (candidate 2, lemma): \begin{lemma}\label{lem:disjoint-contract-delete} If $N \le_m M$, then there exist subsets
                                      $C,D\subseteq E(M)$ such that \[ C\cap D=\varnothing \qquad\text{and}\qquad N = M / C
                                      \setminus D. \] \end{lemma}
4. Lemma (IsMinor.antisymm)
   The lemma must be named `IsMinor.antisymm`.
   Matched text (candidate 3, theorem, label=IsMinor.antisymm): \begin{theorem}[IsMinor.antisymm]\label{thm:minor-order} The minor relation $\le_m$ defines
                                                                a partial order on the class of matroids on $\alpha$. Explicitly: \begin{itemize} \item $N
                                                                \le_m N$ for all $N$ (reflexivity), \item if $N \le_m M$ and $M \le_m P$, then $N \le_m P$
                                                                (transitivity), \item if $N \le_m M$ and $M \le_m N$, then $N = M$ (antisymmetry).
                                                                \end{itemize} \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
