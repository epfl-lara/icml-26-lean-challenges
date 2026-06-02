# Formalization Blueprint: `probability/L3/prob_gen_L3_001`

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
import Mathlib
```

## Required Names

- `BuffonNeedle`

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
open Real MeasureTheory ProbabilityTheory

/-
Formalize in Lean the following named items from Text.

1. Theorem (BuffonNeedle)
   The theorem must be named `BuffonNeedle`.
   Matched text: Theorem(`BuffonNeedle`).

Suppose a short needle of length $\ell$ is dropped onto a paper ruled with equally spaced lines of distance $d \ge \ell$. Then the probability that the needle crosses a line on the paper is $\frac{2\ell}{\pi d}$.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
