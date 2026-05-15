# Formalization Blueprint: `analysis/L2/ana_gen_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
```

## Required Names

- `MeromorphicAt`
- `AnalyticAt.meromorphicAt`

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
open Filter Set
open scoped Topology

/-
Formalize in Lean the following named items from Text.

1. Definition (MeromorphicAt)
   The definition must be named `MeromorphicAt`.
   Matched text (candidate 0, lemma): \begin{lemma} Let $\mathbb{K}$ be a nontrivially normed field and let $E$ be a normed vector
                                      space over $\mathbb{K}$. Let $f : \mathbb{K} \to E$ be an $E$-valued function on $\mathbb K$
                                      and let $x \in \mathbb{K}$. We say that $f$ is \emph{meromorphic at $x$} if there exists $n
                                      \in \mathbb{N}$ such that the function \[ z \longmapsto (z - x)^n f(z) \] is analytic at
                                      $x$. \end{lemma}
2. Lemma (AnalyticAt.meromorphicAt)
   The lemma must be named `AnalyticAt.meromorphicAt`.
   Matched text (candidate 1, theorem, label=AnalyticAt.meromorphicAt): \begin{theorem}[AnalyticAt.meromorphicAt] Let $f : \mathbb K \to E$ and let $x \in \mathbb
                                                                        K$. If $f$ is analytic at $x$, then $f$ is meromorphic at $x$. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
