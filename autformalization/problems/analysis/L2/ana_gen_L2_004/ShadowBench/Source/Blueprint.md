# Formalization Blueprint: `analysis/L2/ana_gen_L2_004`

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
import Mathlib
import Aesop
```

## Required Names

- `exists_seq_finite_rank_strongly_convergent_to`

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
open Filter TopologicalSpace
open scoped Topology

/-
Formalize in Lean the Theorem (exists_seq_finite_rank_strongly_convergent_to) from Text.

The theorem must be named `exists_seq_finite_rank_strongly_convergent_to`.
   Matched text (candidate 0, theorem, label=exists_seq_finite_rank_strongly_convergent_to): \begin{theorem}[exists_seq_finite_rank_strongly_convergent_to] Consider a separable Hilbert
                                                                                             space $\mathcal{H}$. Show that for any bounded operator $T$ there is a sequence $\{T_n\}$ of
                                                                                             bounded operators of finite rank so that $T_n \to T$ strongly as $n \to \infty$.
                                                                                             \end{theorem}
-/
```
