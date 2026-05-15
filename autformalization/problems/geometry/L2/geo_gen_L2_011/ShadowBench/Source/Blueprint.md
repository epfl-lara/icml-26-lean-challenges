# Formalization Blueprint: `geometry/L2/geo_gen_L2_011`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Defs
```

## Required Names

- `isInteriorPoint_of_bijective_mfderiv`

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
open scoped Manifold
open Set

/-
Formalize in Lean the Theorem (isInteriorPoint_of_bijective_mfderiv) from Text.

The theorem must be named `isInteriorPoint_of_bijective_mfderiv`.
   Matched text (candidate 0, theorem, label=isInteriorPoint_of_bijective_mfderiv): \begin{theorem}[isInteriorPoint_of_bijective_mfderiv] Suppose $M$ is a smooth manifold
                                                                                    (without boundary), $N$ is a smooth manifold with boundary, and $F: M \to N$ is smooth. Show
                                                                                    that if $p \in M$ is a point such that $dF_p$ is nonsingular, then $F(p) \in
                                                                                    \operatorname{Int} N$. \end{theorem}
-/
```
