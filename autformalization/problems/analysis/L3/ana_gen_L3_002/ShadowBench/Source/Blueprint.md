# Formalization Blueprint: `analysis/L3/ana_gen_L3_002`

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
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
```

## Required Names

- `open_disc_not_disjoint_union_rectangles`

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
open Euclidean

/-
Formalize in Lean the Theorem (open_disc_not_disjoint_union_rectangles) from Text.

The theorem must be named `open_disc_not_disjoint_union_rectangles`.
   Matched text (candidate 0, theorem, label=open_disc_not_disjoint_union_rectangles): \begin{theorem}[open_disc_not_disjoint_union_rectangles] An open disc in $\mathbb{R}^2$ is
                                                                                       not the disjoint union of open rectangles. \\ \end{theorem}
-/
```
