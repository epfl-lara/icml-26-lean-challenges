# Formalization Blueprint: `analysis/L2/ana_mero_L2_001`

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

- `divisor`
- `divisor_support`
- `divisor_support_locally_finite`

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
Formalize in Lean the following named items from Text.

1. Definition (divisor)
   The definition must be named `divisor`.
   Matched text (candidate 0, definition, label=ABM_analysis_L2_ana_mero_L2_001_item_1): \begin{definition}[ABM_analysis_L2_ana_mero_L2_001_item_1] Let $\mathbb K$ be a nontrivially
                                                                                         normed field and let $E$ be a normed vector space over $\mathbb K$. Let $U \subseteq \mathbb
                                                                                         K$ be a set and let $f : \mathbb K \to E$ be a function. The \emph{divisor} of $f$ on $U$ is
                                                                                         the function \[ \operatorname{div}_U(f) : \mathbb K \longrightarrow \mathbb{Z} \] defined by
                                                                                         \[ \operatorname{div}_U(f)(z) = \begin{cases} \…
2. Definition (divisor_support)
   The definition must be named `divisor_support`.
   Matched text (candidate 1, definition, label=ABM_analysis_L2_ana_mero_L2_001_item_2): \begin{definition}[ABM_analysis_L2_ana_mero_L2_001_item_2] The \emph{support} of the divisor
                                                                                         is \[ \operatorname{supp}(\operatorname{div}_U(f)) = \{ z \in U \mid
                                                                                         \operatorname{div}_U(f)(z) \neq 0 \}. \] Equivalently, \[
                                                                                         \operatorname{supp}(\operatorname{div}_U(f)) = \{ z \in U \mid \operatorname{ord}_z(f) \neq
                                                                                         0 \text{ and } \operatorname{ord}_z(f) \neq \infty \}. \] \end{definition}
3. Theorem (divisor_support_locally_finite)
   The theorem must be named `divisor_support_locally_finite`.
   Matched text (candidate 2, theorem, label=divisor): \begin{theorem}[divisor] If $f$ is meromorphic on $U$, then the support of
                                                       $\operatorname{div}_U(f)$ is locally finite in $U$. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
