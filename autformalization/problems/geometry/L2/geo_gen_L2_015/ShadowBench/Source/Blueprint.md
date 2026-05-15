# Formalization Blueprint: `geometry/L2/geo_gen_L2_015`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.Cone.Basic
```

## Required Names

- `separatingHyperplanes_is_pointed`

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
open InnerProductSpace

/-
Formalize in Lean the Theorem (separatingHyperplanes_is_pointed) from Text.

The theorem must be named `separatingHyperplanes_is_pointed`.
   Matched text (candidate 0, theorem, label=separatingHyperplanes_is_pointed): \begin{theorem}[separatingHyperplanes_is_pointed] Suppose that $C$ and $D$ are disjoint
                                                                                subsets of $\mathbb{R}^n$. Consider the set of $(a, b) \in \mathbb{R}^{n+1}$ for which $a^T
                                                                                x \le b$ for all $x \in C$, and $a^T x \ge b$ for all $x \in D$. Show that this set is a
                                                                                convex cone containing the origin. (which is the singleton $\{0\}$ if there is no hyperplane
                                                                                that separates $C$ and $D$). \end{theorem}
-/
```
