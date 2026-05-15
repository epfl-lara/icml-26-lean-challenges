# Formalization Blueprint: `analysis/L3/ana_gen_L3_008`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `intervalIntegrable_g_and_integral_g_eq_integral`

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
open Set MeasureTheory

/-
Formalize in Lean the Theorem (intervalIntegrable_g_and_integral_g_eq_integral) from Text.

The theorem must be named `intervalIntegrable_g_and_integral_g_eq_integral`.
   Matched text (candidate 0, theorem, label=intervalIntegrable_g_and_integral_g_eq_integral): \begin{theorem}[intervalIntegrable_g_and_integral_g_eq_integral] Suppose $f$ is integrable
                                                                                               on $[0, b]$, and \[ g(x) = \int_x^b \frac{f(t)}{t} dt \quad \text{for } 0 < x \le b. \]
                                                                                               Prove that $g$ is integrable on $[0, b]$ and \[ \int_0^b g(x) dx = \int_0^b f(t) dt. \]
                                                                                               \end{theorem}
-/
```
