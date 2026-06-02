# Formalization Blueprint: `algebra/L2/alg_gen_L2_004`

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
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz
```

## Required Names

- `J`
- `exists_vanishingIdeal_zeroLocus_not_mem_J`

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
/-
Formalize in Lean the following named items from the theorem in the text.

1. Definition (J)
   The definition must be named `J`.
   Matched text (candidate 0, definition):
Let $J = \langle x^2 + y^2 - 1, y - 1\rangle \subseteq \mathbb R[x,y]$.

2. Theorem (exists_vanishingIdeal_zeroLocus_not_mem_J)
   The theorem must be named `exists_vanishingIdeal_zeroLocus_not_mem_J`.
   Matched text (candidate 0, theorem):
\begin{theorem}
Let $J = \langle x^2 + y^2 - 1, y - 1\rangle \subseteq \mathbb R[x,y]$.
Find a polynomial $f \in \mathbf I(\mathbf V(J))$ such that $f \notin J$.
\end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
