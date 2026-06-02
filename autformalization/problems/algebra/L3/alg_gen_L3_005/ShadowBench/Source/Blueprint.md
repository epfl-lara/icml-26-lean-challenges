# Formalization Blueprint: `algebra/L3/alg_gen_L3_005`

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
import Aesop
```

## Required Names

- `I_isPrimary`
- `I_not_infIrred`

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
open MvPolynomial

/-
Formalize in Lean the two named statements from the theorem in the text.

The Lean declarations must be named:
- `I_isPrimary`
- `I_not_infIrred`

Matched text (candidate 0, theorem):
\begin{theorem}
Let $I = \langle x^2, xy, y^2 \rangle \subseteq k[x, y]$.
\begin{enumerate}
    \item[I_isPrimary] $I$ is primary.
    \item[I_not_infIrred] $I = \langle x^2, y \rangle \cap \langle x, y^2 \rangle$ and conclude that $I$ is not irreducible.
\end{enumerate}
\end{theorem}
-/
```
