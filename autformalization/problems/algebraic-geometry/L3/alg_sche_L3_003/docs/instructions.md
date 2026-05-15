# ShadowBench Instructions: `algebraic-geometry/L3/alg_sche_L3_003`

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

- `projective_isProper`

## Formalization Rules

```text
open CategoryTheory AlgebraicGeometry

/-
Formalize in Lean the Theorem (projective_isProper) from Text.

The theorem must be named `projective_isProper`.
   Matched text (candidate 0, theorem, label=projective_isProper): \begin{theorem}[projective_isProper] Let $S$ be a scheme, and let $f : X \to S$ be a
                                                                   projective morphism. Then $f$ is proper. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
