# ShadowBench Instructions: `algebraic-geometry/L3/alg_gen_L3_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Grp_
```

## Expected Declaration Names

- `smooth_of_grpObj_of_isAlgClosed`

## Formalization Rules

```text
open CategoryTheory

/-
Formalize in Lean the Lemma (smooth_of_grpObj_of_isAlgClosed) from Text.

The lemma must be named `smooth_of_grpObj_of_isAlgClosed`.
   Matched text (candidate 0, theorem, label=smooth_of_grpObj_of_isAlgClosed): \begin{theorem}[smooth_of_grpObj_of_isAlgClosed] If $G$ is a group scheme over an
                                                                               algebraically closed field $k$ that is reduced and locally of finite type, then $G$ is
                                                                               smooth over $k$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
