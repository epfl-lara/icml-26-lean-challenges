# Formalization Blueprint: `analysis/L4/ana_func_L4_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `exists_unitary_near_of_approx_unitary`

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
Formalize in Lean the Theorem (exists_unitary_near_of_approx_unitary) from Text.

The theorem must be named `exists_unitary_near_of_approx_unitary`.
   Matched text (candidate 0, theorem, label=exists_unitary_near_of_approx_unitary): \begin{theorem}[exists_unitary_near_of_approx_unitary] Let $\mathcal A$ be a unital
                                                                                     $C^*$-algebra. Show that for any $\varepsilon > 0$ there exists a $\delta_\varepsilon > 0$
                                                                                     such that if $a \in \mathcal A$ obeys \[ \max\left\{ \|a^*a-\mathbf 1\|,\ \|aa^*-\mathbf 1\|
                                                                                     \right\} \le \delta_\varepsilon, \] then there exists a unitary $u \in \mathcal A$ with \[
                                                                                     \|a-u\| \le \varepsilon. \] \end{theorem}
-/
```
