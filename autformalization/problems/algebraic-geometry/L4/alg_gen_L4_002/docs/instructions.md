# ShadowBench Instructions: `algebraic-geometry/L4/alg_gen_L4_002`

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

- `VanishesAt`
- `Locus`
- `ExcessLociCrossings`

## Formalization Rules

```text
open scoped LinearAlgebra.Projectivization

/-
Formalize in Lean the following named items from Text.

1. Definition (VanishesAt)
   The definition must be named `VanishesAt`.
2. Definition (Locus)
   The definition must be named `Locus`.
3. Theorem (ExcessLociCrossings)
   The theorem must be named `ExcessLociCrossings`.
   Matched text (candidate 3, paragraph): Theorem(`ExcessLociCrossings`).

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
