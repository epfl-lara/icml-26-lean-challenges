# Formalization Blueprint: `geometry/L2/geo_gen_L2_020`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `exists_smooth_vectorField_on_graph`

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
open scoped Manifold ContDiff

/-
Formalize in Lean the Theorem (exists_smooth_vectorField_on_graph) from Text.

The theorem must be named `exists_smooth_vectorField_on_graph`.
   Matched text (candidate 0, theorem, label=exists_smooth_vectorField_on_graph): \begin{theorem}[exists_smooth_vectorField_on_graph] Let $M$ be a smooth manifold with or
                                                                                  without boundary, let $N$ be a smooth manifold, and let $f: M \to N$ be a smooth map. Define
                                                                                  $F: M \to M \times N$ by $F(x) = (x, f(x))$. Show that for every $X \in \mathfrak{X}(M)$,
                                                                                  there is a smooth vector field $Y$ on $M \times N$ that is $F$-related to $X$; that is,
                                                                                  $dF_p(X_p) = Y_{F(p)}$ for every $p \in M$. \end{theorem}
-/
```
