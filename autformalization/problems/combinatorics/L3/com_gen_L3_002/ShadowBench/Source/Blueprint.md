# Formalization Blueprint: `combinatorics/L3/com_gen_L3_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: the single generated Lean module for this source document. The document is short, so no split into auxiliary generated files is useful at this stage.
- Root coverage: `ShadowBench.lean` imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so ordinary project builds cover the generated target module.

## Import Plan

```lean
import Mathlib.Combinatorics.Matroid.Minor.Order
```

The direct import is `Mathlib.Combinatorics.Matroid.Minor.Order`, because Mathlib already contains the matroid minor relation, strict minor relation, disjoint contraction/deletion representation theorem, reflexivity/transitivity/antisymmetry lemmas, and the minor-order `PartialOrder` instance. This import itself publicly imports `Mathlib.Combinatorics.Matroid.Minor.Contract`, the starting import from `docs/instructions.md`.

## Suggested Search Modules

- `Mathlib.Combinatorics.Matroid.Minor.Order`: canonical facts `Matroid.IsMinor`, `Matroid.IsStrictMinor`, `Matroid.IsMinor.exists_eq_contract_delete_disjoint`, `Matroid.IsMinor.refl`, `Matroid.IsMinor.trans`, `Matroid.IsMinor.antisymm`.
- `Mathlib.Combinatorics.Matroid.Minor.Contract`: contraction/deletion composition and commutation identities such as `contract_delete_contract_delete'`, plus ground-set facts for contractions.
- `Mathlib.Combinatorics.Matroid.Minor.Delete`: deletion ground-set and deletion identity facts useful for the disjoint-representation proof.

## Candidate Skeleton Review

- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` use the non-required theorem name `IsMinor_exists_eq_contract_delete_disjoint`; those files were not copied as-is.
- `Skeleton4.lean` has the required theorem name `IsMinor.exists_eq_contract_delete_disjoint` and shaped the final declaration names and the use of `Disjoint`/ground-set side conditions as proof hints.
- All skeletons define `IsMinor` with extra side conditions `C ⊆ M.groundSet` and `D ⊆ M.groundSet`. This strengthens source line 17, where `C,D` are arbitrary subsets of the ambient type. The final draft therefore follows the source text and Mathlib's canonical `Matroid.IsMinor` definition instead.
- Mathlib notation uses `N ≤m M` and wide matroid operations `M ／ C ＼ D`. The generated file additionally provides source-style notations `N ≤ₘ M` and `N <ₘ M` for the local names.

## Required Names

- `IsMinor`
- `IsStrictMinor`
- `IsMinor.exists_eq_contract_delete_disjoint`
- `IsMinor_antisymm`

Additional companion declarations used to cover every explicit bullet in source lemma `thm:minor-order`:

- `IsMinor.refl`
- `IsMinor.trans`

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, lines 17-24.
- Planned Lean declarations: `IsMinor`.
- Lean statement/definition:
  ```lean
  def IsMinor {α : Type*} (N M : Matroid α) : Prop :=
    Matroid.IsMinor N M
  ```
- Skeleton candidate used: no skeleton copied as-is; the final definition is the source-accurate version of Mathlib's `Matroid.IsMinor`. Skeletons were rejected for this line because they require `C,D` to lie in the ground set in the definition itself.
- Dependencies: `Matroid`, `Matroid.IsMinor`, matroid contraction/deletion notation from `Mathlib.Combinatorics.Matroid.Minor.Order`.
- Formal statement review: Mathlib's `Matroid.IsMinor N M` unfolds to `∃ C D, N = M ／ C ＼ D`, matching the source statement that `N` is obtained from `M` by contracting some subset `C` and deleting some subset `D` of the ambient type. The local name `IsMinor` is an exact wrapper preserving the required ShadowBench name.
- Source qualifiers:
  - mathematical object class: matroids `N M : Matroid α` on a common ambient type `α`;
  - quantifier order: ambient type `α`, then target minor `N`, then source matroid `M`;
  - parameter domain: subsets `C,D : Set α`;
  - equality condition: `N = M ／ C ＼ D`;
  - side conditions: none beyond `C,D` being subsets of the ambient type by typing;
  - follow-on notation: local notation `N ≤ₘ M` denotes `IsMinor N M`.
- Lean coverage: `IsMinor` covers the existence/equality condition via `Matroid.IsMinor`; the local notation declaration covers the displayed relation notation.
- Scope changes: none. The Lean notation uses Mathlib's wide operators `／` and `＼`, but these are the matroid contraction and deletion operations corresponding to source `/` and `\setminus`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition only; no proof in the source.

### line-26

- Source locator: `docs/source.tex`, lines 26-30.
- Planned Lean declarations: `IsStrictMinor`.
- Lean statement/definition:
  ```lean
  def IsStrictMinor {α : Type*} (N M : Matroid α) : Prop :=
    IsMinor N M ∧ ¬ IsMinor M N
  ```
- Skeleton candidate used: Skeleton4 shaped the exact local declaration name and strict-minor shape; this definition is source-checked against lines 26-30.
- Dependencies: `IsMinor`.
- Formal statement review: the source says `N` is a strict minor of `M` iff `N` is a minor of `M` and `M` is not a minor of `N`; the Lean definition states exactly this conjunction.
- Source qualifiers:
  - mathematical object class: matroids `N M : Matroid α` on a common ambient type `α`;
  - quantifier order: ambient type `α`, then `N`, then `M`;
  - parameter domain: two matroids on `α`;
  - output codomain: `Prop`;
  - equality/image condition: inherited through `IsMinor`;
  - side conditions: `IsMinor N M` and negation of `IsMinor M N`;
  - follow-on notation: local notation `N <ₘ M` denotes `IsStrictMinor N M`.
- Lean coverage: `IsStrictMinor` covers the strict-minor definition; the local notation declaration covers the displayed relation notation.
- Scope changes: none.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition only; no proof in the source.

### lem:disjoint-contract-delete

- Source locator: `docs/source.tex`, lines 32-70.
- Planned Lean declarations: `IsMinor.exists_eq_contract_delete_disjoint`.
- Lean statement:
  ```lean
  theorem IsMinor.exists_eq_contract_delete_disjoint {α : Type*} {N M : Matroid α}
      (h : N ≤ₘ M) :
      ∃ C D : Set α, C ⊆ M.E ∧ D ⊆ M.E ∧ (C ∩ D = ∅) ∧
        (N = Matroid.delete (Matroid.contract M C) D)
  ```
- Skeleton candidate used: Skeleton4 shaped the exact declaration name and the ground-set/disjoint witness shape. The final statement uses `M.E`, Mathlib's ground set field, and `C ∩ D = ∅` to match the source formula exactly; Mathlib's existing theorem gives the same statement with `Disjoint C D`.
- Dependencies: `IsMinor`; matroid ground set `M.E`; contraction/deletion operations; Mathlib theorem `Matroid.IsMinor.exists_eq_contract_delete_disjoint`; set fact converting `Disjoint C D` to `C ∩ D = ∅`.
- Formal statement review: The source assumes `N ≤_m M` and concludes existence of `C,D ⊆ E(M)` with `C ∩ D = ∅` and `N = M / C \setminus D`. The Lean statement assumes `h : N ≤ₘ M`; uses `C,D : Set α`; uses `C ⊆ M.E` and `D ⊆ M.E` for `C,D ⊆ E(M)`; states `C ∩ D = ∅`; and states `N = Matroid.delete (Matroid.contract M C) D`, the function form of `M ／ C ＼ D`. This is an exact formal rendering, modulo Mathlib's notation for matroid operations and ground sets.
- Source qualifiers:
  - mathematical object class: matroids `N M : Matroid α`;
  - quantifier order: `α`, then implicit `N M`, then hypothesis `N ≤ₘ M`, then existential witnesses `C D`;
  - parameter domain: `C,D : Set α`;
  - output codomain: existential proposition;
  - equality/image condition: `N = Matroid.delete (Matroid.contract M C) D`;
  - side conditions: `C ⊆ M.E`, `D ⊆ M.E`, `C ∩ D = ∅`;
  - follow-on claims: none.
- Lean coverage: all qualifiers appear directly in `IsMinor.exists_eq_contract_delete_disjoint`.
- Scope changes: none.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text (verbatim, source lines 41-70):
  ```text
  Assume $N \le_m M$. By definition, there exist $C_0,D_0\subseteq \alpha$ with
  \[
  N = M/C_0 \setminus D_0.
  \]
  Since deletion and contraction only affect elements of the ground set, we may replace
  $C_0$ and $D_0$ by $C_0\cap E(M)$ and $D_0\cap E(M)$ and hence assume
  $C_0,D_0\subseteq E(M)$.

  Now set
  \[
  C := C_0,
  \qquad
  D := D_0\setminus C_0.
  \]
  Then $C,D\subseteq E(M)$ and $C\cap D=\varnothing$.

  It remains to show that deleting $D_0$ after contracting $C_0$ is the same as deleting
  $D_0\setminus C_0$ after contracting $C_0$.
  After contracting $C_0$, the ground set becomes $E(M)\setminus C_0$, so elements of
  $D_0\cap C_0$ are not present in $M/C_0$ and deleting them has no effect. Hence
  \[
  (M/C_0)\setminus D_0 \;=\; (M/C_0)\setminus (D_0\setminus C_0).
  \]
  Therefore
  \[
  N \;=\; M/C \setminus D,
  \]
  with $C,D\subseteq E(M)$ disjoint, as required.
  ```
- Prover notes: unfold the local wrapper `IsMinor` to Mathlib's `Matroid.IsMinor`, use `Matroid.IsMinor.exists_eq_contract_delete_disjoint h` to obtain witnesses with `Disjoint C D`, and convert disjointness to `C ∩ D = ∅` using the standard `Set` disjoint/intersection-empty lemma.

### thm:minor-order

- Source locator: `docs/source.tex`, lines 72-149.
- Planned Lean declarations: `IsMinor.refl`, `IsMinor.trans`, `IsMinor_antisymm`.
- Lean signatures:
  - `theorem IsMinor.refl {α : Type*} (N : Matroid α) : N ≤ₘ N`
  - `theorem IsMinor.trans {α : Type*} {N M P : Matroid α} (hNM : N ≤ₘ M) (hMP : M ≤ₘ P) : N ≤ₘ P`
  - `theorem IsMinor_antisymm {α : Type*} {N M : Matroid α} (hNM : N ≤ₘ M) (hMN : M ≤ₘ N) : N = M`
- Skeleton candidate used: Skeleton4 shaped the required exact declaration `IsMinor_antisymm`, but Skeleton4 only states the antisymmetry bullet. The final draft adds `IsMinor.refl` and `IsMinor.trans` so that the reflexivity and transitivity bullets in the source are also formalized.
- Dependencies: `IsMinor`; `IsMinor.exists_eq_contract_delete_disjoint` for the source proof strategy; Mathlib facts `Matroid.IsMinor.refl`, `Matroid.IsMinor.trans`, `Matroid.IsMinor.antisymm` for the eventual Lean proofs.
- Formal statement review: The source lemma asserts that the minor relation is a partial order and then spells out reflexivity, transitivity, and antisymmetry. The Lean draft represents those three explicit bullets as three theorem declarations. The required name `IsMinor_antisymm` is preserved for the antisymmetry bullet; the companion declarations carry the other two bullets.
- Source qualifiers:
  - mathematical object class: all matroids on a fixed ambient type `α`;
  - quantifier order: reflexivity quantifies one matroid `N`; transitivity quantifies `N M P` and assumes `N ≤ₘ M` then `M ≤ₘ P`; antisymmetry quantifies `N M` and assumes both directions;
  - parameter domain: `Matroid α`;
  - output codomain: propositions expressing minor relation or equality of matroids;
  - equality/image condition: antisymmetry conclusion `N = M`;
  - side conditions: the minor hypotheses in the transitivity and antisymmetry bullets;
  - follow-on claim: together these clauses state that the relation is a partial order. Mathlib already has a `PartialOrder (Matroid α)` instance for the canonical `≤m` relation.
- Lean coverage: `IsMinor.refl` covers the reflexivity bullet; `IsMinor.trans` covers the transitivity bullet; `IsMinor_antisymm` covers the antisymmetry/equality bullet; the source's overall partial-order claim is covered by this trio and the Mathlib import's canonical instance.
- Scope changes: the one source lemma is split into three Lean theorem declarations to preserve all explicit bullets while keeping the required exact name `IsMinor_antisymm` for the antisymmetry clause. No mathematical weakening or strengthening is intended.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text (verbatim, source lines 82-149):
  ```text
  \textbf{Reflexivity.}
  For any matroid $N$, taking $C=D=\varnothing$ gives
  \[
  N = N/\varnothing \setminus \varnothing,
  \]
  so $N \le_m N$.

  \medskip
  \textbf{Transitivity.}
  Assume $N \le_m M$ and $M \le_m P$.
  By Lemma~\ref{lem:disjoint-contract-delete}, choose disjoint $C_1,D_1\subseteq E(M)$ and
  disjoint $C_2,D_2\subseteq E(P)$ such that
  \[
  N = M/C_1 \setminus D_1,
  \qquad
  M = P/C_2 \setminus D_2.
  \]
  Since $M = P/C_2 \setminus D_2$ with $C_2\cap D_2=\varnothing$, we have
  \[
  E(M)=E(P)\setminus(C_2\cup D_2),
  \]
  so $C_1\cup D_1\subseteq E(M)$ implies $C_1\cap(C_2\cup D_2)=\varnothing$ and
  $D_1\cap(C_2\cup D_2)=\varnothing$. In particular, all of $C_1,D_1,C_2,D_2$ are pairwise
  disjoint as needed below.

  Substituting $M = P/C_2\setminus D_2$ into the expression for $N$ gives
  \[
  N \;=\; \Bigl( (P/C_2\setminus D_2)/C_1 \Bigr)\setminus D_1.
  \]
  Using the standard identities for disjoint deletions and contractions
  \[
  (M\setminus T_1)\setminus T_2 = M\setminus (T_1\cup T_2),\qquad
  (M/T_1)/T_2 = M/(T_1\cup T_2),\qquad
  (M/T_1)\setminus T_2 = (M\setminus T_2)/T_1,
  \]
  we may commute and combine these operations (since all the relevant sets are disjoint) to obtain
  \[
  N \;=\; P/(C_2\cup C_1)\setminus (D_2\cup D_1).
  \]
  Hence $N \le_m P$.

  \medskip
  \textbf{Antisymmetry.}
  Assume $N \le_m M$ and $M \le_m N$.
  By Lemma~\ref{lem:disjoint-contract-delete}, write
  \[
  N = M/C \setminus D
  \quad\text{with}\quad
  C,D\subseteq E(M),\ \ C\cap D=\varnothing.
  \]
  Then the ground set is
  \[
  E(N)=E(M)\setminus(C\cup D).
  \]
  In particular $E(N)\subseteq E(M)$. Symmetrically, $E(M)\subseteq E(N)$, hence
  $E(M)=E(N)$. Therefore
  \[
  E(M)=E(M)\setminus(C\cup D),
  \]
  which forces $C\cup D=\varnothing$, so $C=D=\varnothing$. Thus
  \[
  N = M/\varnothing\setminus\varnothing = M,
  \]
  proving antisymmetry.

  Since $\le_m$ is reflexive, transitive, and antisymmetric, it is a partial order.
  ```
- Prover notes: because `IsMinor` is a wrapper around Mathlib's `Matroid.IsMinor`, the proof can likely be short: unfold `IsMinor`/the local notation and use `Matroid.IsMinor.refl`, `Matroid.IsMinor.trans`, and `Matroid.IsMinor.antisymm`. If proving by source proof instead, use `IsMinor.exists_eq_contract_delete_disjoint`, ground-set inclusions, and Mathlib contraction/deletion composition lemmas from `Matroid.Minor.Contract`.

## Statement Verification Gate

This blueprint and `ShadowBench/Source/Main.lean` are ready for an independent statement/source review pass. The review should compare each source locator above with the Lean declaration and check the source-proof notes plus Lean doc-comment nudges. The formalizer intentionally leaves every `Statement verification status` entry awaiting that review.

Suggested prover command after the statement/source review pass:

```text
/prove ShadowBench/Source/Main.lean
```
