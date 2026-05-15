# ShadowBench Instructions: `topology/L2/top_gen_L2_016`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.AlgebraicTopology.MooreComplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Idempotents.FunctorCategories
```

## Expected Declaration Names

- `inclusionOfMooreComplexMap`
- `inclusionOfMooreComplexMap_f`
- `inclusionOfMooreComplex`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
