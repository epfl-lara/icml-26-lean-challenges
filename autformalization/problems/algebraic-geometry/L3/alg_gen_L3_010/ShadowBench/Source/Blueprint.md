# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_010`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `isAffineOpen_inf_preimage`

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
open CategoryTheory Opposite
open TopologicalSpace

/-
Formalize in Lean the Theorem (isAffineOpen_inf_preimage) from Text.

The theorem must be named `isAffineOpen_inf_preimage`.
   Matched text (candidate 0, theorem, label=isAffineOpen_inf_preimage): \begin{theorem}[isAffineOpen_inf_preimage] Let \(Y\) be a separated scheme, and let \(f:X\to
                                                                         Y\) be a morphism. For every affine open subset \(U\) of \(X\) and every affine open subset
                                                                         \(V\) of \(Y\), \(U\cap f^{-1}(V)\) is affine. \end{theorem}
-/
```
