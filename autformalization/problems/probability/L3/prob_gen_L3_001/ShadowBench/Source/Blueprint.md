# Formalization Blueprint: `probability/L3/prob_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `BuffonNeedle`
- `BuffonProb`

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
open Real MeasureTheory ProbabilityTheory

/-
Formalize in Lean the following named items from Text.


0. Definition (Ω_pos)
   The definition must be named `Ω_pos`.
   Matched text (candidate 0, paragraph): Theorem(`BuffonNeedle`).
1. Definition (Ω_angle)
   The definition must be named `Ω_angle`.
   Matched text (candidate 0, paragraph): Theorem(`BuffonNeedle`).
2. Definition (Ω)
   The definition must be named `Ω`.
   Matched text (candidate 1, paragraph): Suppose a short needle of length $\ell$ is dropped onto a paper ruled with equally spaced
                                          lines of distance $d \ge \ell$. Then the probability that the needle crosses a line on the
                                          paper is $\frac{2\ell}{\pi d}$.
3. Definition (BuffonProb)
   The definition must be named `BuffonProb`.
   Matched text (candidate 2, paragraph): Proof.
4. Theorem (BuffonNeedle)
   The theorem must be named `BuffonNeedle`.
   Matched text (candidate 3, paragraph): We can assume the uniform probability distribution over $[0, d] \times [0, \pi]$, where each
                                          component means the midpoint position relative to the closest lower line and the angle
                                          relative to a fixed direction of the ruling respectively. Then the needle crosses a line
                                          with angle $\theta$ exactly when its height $y$ of midpoint is lower than $\frac{\ell \sin
                                          \theta}{2}$ or higher than $d - \frac{\ell \sin \theta}{2}$…

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
