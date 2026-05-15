# Formalization Blueprint: `topology/L2/top_gen_L2_015`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Abelian.Basic
```

## Required Names

- `normalizedMooreComplex`
- `normalizedMooreComplex_objD`

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
open CategoryTheory CategoryTheory.Limits
open Opposite
open scoped Simplicial
open CategoryTheory.Subobject

/-
Formalize in Lean the following named items from Text.

1. Definition (normalizedMooreComplex)
   The definition must be named `normalizedMooreComplex`.
   Matched text (candidate 0, theorem): \begin{theorem} Let $C$ be an abelian category. We define the normalized Moore complex to be
                                        a functor \begin{align*} N_\bullet: \mathbf{sC} \to \mathbf{Ch}_{\ge 0}(C), \quad X \mapsto
                                        N_\bullet(X) \end{align*} from the category $\mathbf{sC}$ of simplicial objects of $C$ to
                                        the category $\mathbf{Ch}_{\ge 0}(C)$ of chain complexes in $C$ where \begin{align*} N_n(X)
                                        = \begin{cases} X_0, &\text{for $n=0$}\\ \bigcap_{i=…
2. Theorem (normalizedMooreComplex_objD)
   The theorem must be named `normalizedMooreComplex_objD`.
   Matched text (candidate 1, theorem, label=normalizedMooreComplex_objD): \begin{theorem}[normalizedMooreComplex_objD] $N_\bullet$ is a well-defined functor.
                                                                           \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
