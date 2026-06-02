# ShadowBench Instructions: `topology/L2/top_gen_L2_016`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.AlgebraicTopology.MooreComplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Idempotents.FunctorCategories
```

## Expected Declaration Names

- `alternatingFaceMapComplex`
- `map_f`
- `inclusionOfMooreComplex`

## Formalization Rules

```text
open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject
open CategoryTheory.Preadditive CategoryTheory.Category CategoryTheory.Idempotents
open Opposite
open Simplicial

/-
Formalize in Lean the following named items from Text.

1. Definition (alternatingFaceMapComplex)
   The definition must be named `alternatingFaceMapComplex`.
   Matched text (candidate 0, definition, label=alternatingFaceMapComplex): \begin{definition}[alternatingFaceMapComplex] Let $C$ be a preadditive category. We define
                                                                            alternating face map complex to be a functor \[ C_\bullet: \mathbf{sC} \to \mathbf{Ch}_{\ge
                                                                            0}(C), \quad X \mapsto C_\bullet(X) \] from the category $\mathbf{sC}$ of simplicial objects
                                                                            of $C$ to the category $\mathbf{Ch}_{\ge 0}(C)$ of chain complexes in $C$ where $C_n(X) =
                                                                            X_n$ for each $n=0,1,\cdots$, and the differentials $…
2. Theorem (map_f)
   The theorem must be named `map_f`.
   Matched text (candidate 1, theorem, label=map_f): \begin{theorem}[map_f] The functor $C_\bullet$ is a well-defined functor. \end{theorem}
3. Theorem (inclusionOfMooreComplex)
   The theorem must be named `inclusionOfMooreComplex`.
   Matched text (candidate 2, theorem, label=inclusionOfMooreComplex): \begin{theorem}[inclusionOfMooreComplex] Let $C$ be an abelian category. Then there is an
                                                                       inclusion $N_\bullet \hookrightarrow C_\bullet $ from the normalized Moore complex into the
                                                                       alternating face map complex, as a natural transformation of functors. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
