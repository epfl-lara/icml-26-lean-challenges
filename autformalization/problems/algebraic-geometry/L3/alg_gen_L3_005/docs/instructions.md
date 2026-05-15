# ShadowBench Instructions: `algebraic-geometry/L3/alg_gen_L3_005`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib
```

## Expected Declaration Names

- `IsProjective`
- `projective_isProper`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
