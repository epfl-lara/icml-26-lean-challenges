# Formalization Blueprint: `analysis/L2/ana_mero_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp
```

## Required Names

- `ABM_analysis_L2_ana_mero_L2_001_item_1`
- `ABM_analysis_L2_ana_mero_L2_001_item_2`
- `divisor`

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
open Filter Topology

/-
Formalize in Lean the following named items from Text.

1. Definition (ABM_analysis_L2_ana_mero_L2_001_item_1)
   The definition must be named `ABM_analysis_L2_ana_mero_L2_001_item_1`.
   Matched text (candidate 0, definition): \begin{definition} Let $\mathbb K$ be a nontrivially normed field and let $E$ be a normed
                                           vector space over $\mathbb K$. Let $U \subseteq \mathbb K$ be a set and let $f : \mathbb K
                                           \to E$ be a function. The \emph{divisor} of $f$ on $U$ is the function \[
                                           \operatorname{div}_U(f) : \mathbb K \longrightarrow \mathbb{Z} \] defined by \[
                                           \operatorname{div}_U(f)(z) = \begin{cases} \operatorname{ord}_z(f), & \text{if $f$ i…
2. Definition (ABM_analysis_L2_ana_mero_L2_001_item_2)
   The definition must be named `ABM_analysis_L2_ana_mero_L2_001_item_2`.
   Matched text (candidate 1, definition): \begin{definition} The \emph{support} of the divisor is \[
                                           \operatorname{supp}(\operatorname{div}_U(f)) = \{ z \in U \mid \operatorname{div}_U(f)(z)
                                           \neq 0 \}. \] Equivalently, \[ \operatorname{supp}(\operatorname{div}_U(f)) = \{ z \in U
                                           \mid \operatorname{ord}_z(f) \neq 0 \text{ and } \operatorname{ord}_z(f) \neq \infty \}. \]
                                           \end{definition}
3. Definition (divisor)
   The definition must be named `divisor`.
   Matched text (candidate 2, definition, label=divisor): \begin{definition}[divisor] If $f$ is meromorphic on $U$, then the support of
                                                          $\operatorname{div}_U(f)$ is locally finite in $U$. \end{definition}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
