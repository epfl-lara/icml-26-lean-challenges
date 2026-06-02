# Formalization Blueprint: `analysis/L2/ana_mero_L2_002`

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
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp
```

## Required Names

- `min_divisor_le_divisor_add`

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
open Filter Topology

/-
Formalize in Lean the Theorem (min_divisor_le_divisor_add) from Text.

The theorem must be named `min_divisor_le_divisor_add`.
   Matched text (candidate 0, theorem, label=min_divisor_le_divisor_add): \begin{theorem}[min_divisor_le_divisor_add] Let $f_1,f_2 : \mathbb K \to E$ be meromorphic
                                                                          on a set $U \subseteq \mathbb K$, and let $z \in U$. Assume that the order of $f_1+f_2$ at
                                                                          $z$ is finite. Then \[
                                                                          \min\bigl(\operatorname{div}_U(f_1)(z),\operatorname{div}_U(f_2)(z)\bigr) \;\le\;
                                                                          \operatorname{div}_U(f_1+f_2)(z). \] \end{theorem}
-/
```
