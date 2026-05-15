# Formalization Blueprint: `analysis/L3/ana_gen_L3_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `diagonal_compact_iff_tendsto_zero`

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
open Filter
open scoped Topology

/-
Formalize in Lean the Theorem (diagonal_compact_iff_tendsto_zero) from Text.

The theorem must be named `diagonal_compact_iff_tendsto_zero`.
   Matched text (candidate 0, theorem, label=diagonal_compact_iff_tendsto_zero): \begin{theorem}[diagonal_compact_iff_tendsto_zero] Suppose $T$ is a bounded operator on a
                                                                                 Hilbert space $\mathcal{H}$ which is diagonal with respect to an orthonormal basis
                                                                                 $\{\varphi_k\}_{k=1}^{\infty}$, that is, \[ T\varphi_k = \lambda_k \varphi_k . \] Then $T$
                                                                                 is compact if and only if $\lambda_k \to 0$. \end{theorem}
-/
```
