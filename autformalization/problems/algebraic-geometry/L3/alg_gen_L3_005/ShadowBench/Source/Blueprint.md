# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `IsProjective`
- `projective_isProper`

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
open CategoryTheory AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Theorem (projectiveSpaceπ)
   The theorem must be named `projectiveSpaceπ`.
   Matched text (candidate 0, theorem, label=Projective morphism): \begin{theorem}[Projective morphism] Let $f : X \to S$ be a morphism of schemes. We say that
                                                                   $f$ is \emph{projective} (in the Hartshorne, or $H$-projective, sense) if there exists an
                                                                   integer $n \ge 0$ and a closed immersion \[ i : X \hookrightarrow \mathbf{P}^n_S \] over $S$
                                                                   such that \[ f = \pi \circ i, \] where $\pi : \mathbf{P}^n_S \to S$ is the structure
                                                                   morphism. \end{theorem}
2. Definition (IsProjective)
   The definition must be named `IsProjective`.
   Matched text (candidate 1, theorem): \begin{theorem} Let $S$ be a scheme and $n \ge 0$. The structure morphism \[ \pi :
                                        \mathbf{P}^n_S \to S \] is proper. \end{theorem}
3. Theorem (projective_isProper)
   The theorem must be named `projective_isProper`.
   Matched text (candidate 2, theorem, label=projective_isProper): \begin{theorem}[projective_isProper] Every projective morphism is proper. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
