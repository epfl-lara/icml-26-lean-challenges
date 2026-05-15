# Formalization Blueprint: `algebra/L2/alg_gen_L2_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz
```

## Required Names

- `ABM_algebra_L2_alg_gen_L2_006_item_1`

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
open scoped BigOperators
open MvPolynomial

/-
Formalize in Lean the Theorem (ABM_algebra_L2_alg_gen_L2_006_item_1) from Text.

The theorem must be named `ABM_algebra_L2_alg_gen_L2_006_item_1`.
   Matched text (candidate 0, theorem, label=Ch.\ 4 \S 2, Exercise 5): \begin{theorem}[Ch.\ 4 \S 2, Exercise 5] Prove that ideal-variety correspondence is
                                                                       inclusion-reversing, i.e., if $I_1 \subseteq I_2$ are ideals, then $\mathbf V(I_1) \supseteq
                                                                       \mathbf V(I_2)$, and similarly, if $V_1 \subseteq V_2$ are affine algebraic sets, then
                                                                       $\mathbf I(V_1) \supseteq \mathbf I(V_2)$. Also prove that $\mathbf V(\sqrt{I})=\mathbf
                                                                       V(I)$ for any ideal $I$. \end{theorem}
-/
```
