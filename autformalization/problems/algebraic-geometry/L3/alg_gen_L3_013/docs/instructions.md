# ShadowBench Instructions: `algebraic-geometry/L3/alg_gen_L3_013`

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

- `IsQuasiFiniteModule`
- `isolated_in_fiber_iff_stalk_quasiFinite`

## Formalization Rules

```text
/-
Formalize in Lean the following items from Text.

1. Definition (IsQuasiFiniteModule)
   The definition must be named `IsQuasiFiniteModule`.
2. Theorem (isolated_in_fiber_iff_stalk_quasiFinite)
   The theorem must be named `isolated_in_fiber_iff_stalk_quasiFinite`.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
