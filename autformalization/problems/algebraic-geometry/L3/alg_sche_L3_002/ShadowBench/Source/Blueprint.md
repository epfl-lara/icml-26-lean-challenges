# Formalization Blueprint: `algebraic-geometry/L3/alg_sche_L3_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `Projective`
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
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Definition (Projective)
   The definition must be named `Projective`.
   Matched text (candidate 0, definition): \begin{definition} A morphism $f : X \to S$ is projective if there exists an integer $n \ge
                                           0$ and a closed immersion \[ i : X \hookrightarrow \mathbb{P}^n_S \] such that $f$ factors
                                           as \[ X \xrightarrow{i} \mathbb{P}^n_S \xrightarrow{\pi} S, \] where $\pi$ is the structure
                                           morphism. \end{definition}
2. Theorem (projective_isProper)
   The theorem must be named `projective_isProper`.
   Matched text (candidate 1, theorem, label=projective_isProper): \begin{theorem}[projective_isProper] Let $S$ be a scheme, and let $f : X \to S$ be a
                                                                   projective morphism. Then $f$ is proper. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
