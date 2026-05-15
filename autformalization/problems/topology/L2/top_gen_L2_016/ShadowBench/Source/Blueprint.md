# Formalization Blueprint: `topology/L2/top_gen_L2_016`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.AlgebraicTopology.MooreComplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Idempotents.FunctorCategories
```

## Required Names

- `inclusionOfMooreComplexMap`
- `inclusionOfMooreComplexMap_f`
- `inclusionOfMooreComplex`

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
open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject
open CategoryTheory.Preadditive CategoryTheory.Category CategoryTheory.Idempotents
open Opposite
open Simplicial

/-
Formalize in Lean the following named items from Text.

1. Definition (inclusionOfMooreComplexMap)
   The definition must be named `inclusionOfMooreComplexMap`.
   Matched text (candidate 0, definition): \begin{definition} Let $C$ be a preadditive category. We define alternating face map complex
                                           to be a functor \[ C_\bullet: \mathbf{sC} \to \mathbf{Ch}_{\ge 0}(C), \quad X \mapsto
                                           C_\bullet(X) \] from the category $\mathbf{sC}$ of simplicial objects of $C$ to the category
                                           $\mathbf{Ch}_{\ge 0}(C)$ of chain complexes in $C$ where $C_n(X) = X_n$ for each
                                           $n=0,1,\cdots$, and the differentials $d_n:C_n(X) \to C_{n-1}(X)$…
2. Theorem (inclusionOfMooreComplexMap_f)
   The theorem must be named `inclusionOfMooreComplexMap_f`.
   Matched text (candidate 1, lemma): \begin{lemma} The functor $C_\bullet$ is a well-defined functor. \end{lemma}
3. Definition (inclusionOfMooreComplex)
   The definition must be named `inclusionOfMooreComplex`.
   Matched text (candidate 2, definition, label=inclusionOfMooreComplex): \begin{definition}[inclusionOfMooreComplex] Let $C$ be an abelian category. Then there is an
                                                                          inclusion $N_\bullet \hookrightarrow C_\bullet $ from the normalized Moore complex into the
                                                                          alternating face map complex, as a natural transformation of functors. \end{definition}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
