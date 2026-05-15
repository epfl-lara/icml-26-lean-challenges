# Formalization Blueprint: `geometry/L2/geo_gen_L2_019`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `X`

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
Formalize in Lean the Definition (X) from Text.

The definition must be named `X`.
   Matched text (candidate 0, definition, label=X): \begin{definition}[X] Proposition 8.19 states that if $F: M \to N$ is a diffeomorphism and
                                                    $X$ is a smooth vector field on $M$, then there is a unique smooth vector field $Y$ on $N$
                                                    such that $dF_p (X_p) = Y_{F(p)}$ for every $p \in M$. Show that this can be false if $F$ is
                                                    assumed only to be smooth and bijective: take $F: \mathbb{R} \to \mathbb{R}$ defined by
                                                    $F(x) = x^3$ and $X = d/dx$ on $\mathbb{R}$. \end{defini…
-/
```
