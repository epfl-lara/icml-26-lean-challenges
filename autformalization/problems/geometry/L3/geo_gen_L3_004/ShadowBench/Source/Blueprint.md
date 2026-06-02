# Formalization Blueprint: `geometry/L3/geo_gen_L3_004`

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

- `smoothVectorField_infinite_dimensional`

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
open scoped Manifold ContDiff

/-
Formalize in Lean the Theorem (smoothVectorField_infinite_dimensional) from Text.

The theorem must be named `smoothVectorField_infinite_dimensional`.
   Matched text (candidate 0, theorem, label=smoothVectorField_infinite_dimensional): \begin{theorem}[smoothVectorField_infinite_dimensional] Let $M$ be a nonempty positive-
                                                                                      dimensional smooth manifold with or without boundary. Then $\mathfrak{X}(M)$, the space of
                                                                                      smooth vector fields on $M$, is infinite-dimensional. \end{theorem}
-/
```
