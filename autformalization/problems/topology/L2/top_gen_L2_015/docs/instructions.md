# ShadowBench Instructions: `topology/L2/top_gen_L2_015`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Abelian.Basic
```

## Expected Declaration Names

- `normalizedMooreComplex`
- `normalizedMooreComplex_objD`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
