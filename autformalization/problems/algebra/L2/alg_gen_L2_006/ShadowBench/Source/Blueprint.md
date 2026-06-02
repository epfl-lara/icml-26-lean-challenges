# Formalization Blueprint: `algebra/L2/alg_gen_L2_006`

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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz
```

## Required Names

- `zeroLocus_subset_of_ideal_le`
- `vanishingIdeal_le_of_subset`
- `zeroLocus_radical_eq_zeroLocus`

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
open scoped BigOperators
open MvPolynomial

/-
Formalize in Lean the following named statements from the theorem in the text.

The Lean declarations must be named exactly:
- `zeroLocus_subset_of_ideal_le`
- `vanishingIdeal_le_of_subset`
- `zeroLocus_radical_eq_zeroLocus`

Matched text (candidate 0, theorem):
\begin{theorem}
Prove that the ideal-variety correspondence is inclusion-reversing, i.e.,
if $I_1 \subseteq I_2$ are ideals, then $\mathbf V(I_1) \supseteq \mathbf V(I_2)$,
and similarly, if $V_1 \subseteq V_2$ are affine algebraic sets, then
$\mathbf I(V_1) \supseteq \mathbf I(V_2)$.
Also prove that $\mathbf V(\sqrt{I})=\mathbf V(I)$ for any ideal $I$.
\end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
