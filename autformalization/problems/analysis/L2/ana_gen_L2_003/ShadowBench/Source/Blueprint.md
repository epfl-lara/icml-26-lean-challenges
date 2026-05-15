# Formalization Blueprint: `analysis/L2/ana_gen_L2_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.Calculus.LocalExtr.Basic
```

## Required Names

- `saddle_sections_hasFDerivAt_eq_zero`

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
/-
Formalize in Lean the Theorem (saddle_sections_hasFDerivAt_eq_zero) from Text.

The theorem must be named `saddle_sections_hasFDerivAt_eq_zero`.
   Matched text (candidate 0, theorem, label=saddle_sections_hasFDerivAt_eq_zero): \begin{theorem}[saddle_sections_hasFDerivAt_eq_zero] Suppose $f : \mathbb{R}^n \times
                                                                                   \mathbb{R}^m \to \mathbb{R}$ satisfies the \textit{saddle-point property} at $(\tilde{x},
                                                                                   \tilde{z})$: for all $x \in \mathbb{R}^n$ and $z \in \mathbb{R}^m$, \[ f(\tilde{x}, z) \le
                                                                                   f(\tilde{x}, \tilde{z}) \le f(x, \tilde{z}). \] If the $x$-section $x \mapsto f(x,
                                                                                   \tilde{z})$ is differentiable at $\tilde{x}$, and the $z$-section $z…
-/
```
