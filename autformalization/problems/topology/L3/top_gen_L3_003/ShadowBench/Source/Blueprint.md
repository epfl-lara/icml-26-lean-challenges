# Formalization Blueprint: `topology/L3/top_gen_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.LocalAtTarget
```

## Required Names

- `isProperMap_proj_iff_compactSpace`

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
open TopologicalSpace

/-
Formalize in Lean the Theorem (isProperMap_proj_iff_compactSpace) from Text.

The theorem must be named `isProperMap_proj_iff_compactSpace`.
   Matched text (candidate 0, theorem, label=isProperMap_proj_iff_compactSpace): \begin{theorem}[isProperMap_proj_iff_compactSpace] Suppose $\pi : E \to M$ is a fiber bundle
                                                                                 with fiber $F$. Then $\pi$ is a proper map if and only if $F$ is compact. \end{theorem}
-/
```
