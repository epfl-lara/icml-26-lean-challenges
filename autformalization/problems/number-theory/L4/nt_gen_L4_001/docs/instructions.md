# ShadowBench Instructions: `number-theory/L4/nt_gen_L4_001`

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

- `MertensTheorem0`
- `MertensTheorem1`
- `MertensTheorem2`
- `MeisselMertensConstant`

## Formalization Rules

```text
open Real
open scoped ArithmeticFunction

/-
Formalize in Lean the following named items from Text.

1. Theorem (MertensTheorem0)
   The theorem must be named `MertensTheorem0`.
   Matched text (candidate 0, paragraph): Theorem(`MertensTheorem0`).
2. Theorem (MertensTheorem1)
   The theorem must be named `MertensTheorem1`.
   Matched text (candidate 1, paragraph): Theorem(`MertensTheorem1`).
3. Theorem (MertensTheorem2)
   The theorem must be named `MertensTheorem2`.
   Matched text (candidate 2, paragraph): Theorem(`MertensTheorem2`).
4. Definition (MeisselMertensConstant)
   The definition must be named `MeisselMertensConstant`.
   Matched text (candidate 3, paragraph): Definition(`MeisselMertensConstant`).

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
