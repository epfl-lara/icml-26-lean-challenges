# Formalization Blueprint: `analysis/L4/ana_func_L4_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `exists_projection_near_of_approx_selfadj_idempotent`

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
open scoped Topology

/-
Formalize in Lean the Theorem (exists_projection_near_of_approx_selfadj_idempotent) from Text.

The theorem must be named `exists_projection_near_of_approx_selfadj_idempotent`.
   Matched text (candidate 0, theorem, label=exists_projection_near_of_approx_selfadj_idempotent): \begin{theorem}[exists_projection_near_of_approx_selfadj_idempotent] Let $\mathcal A$ be a
                                                                                                   $C^*$-algebra. Show that for any $\varepsilon > 0$ there exists a $\delta_\varepsilon > 0$
                                                                                                   such that if $a \in \mathcal A$ obeys \[ \max\left\{\|a-a^*\|,\ \|a^2-a\|\right\}\le
                                                                                                   \delta_\varepsilon, \] then there exists a self-adjoint projection $p\in \mathcal A$ with \[
                                                                                                   \|a-p\|\le \varepsilon. \] \end{theorem}
-/
```
