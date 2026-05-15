# ShadowBench Instructions: `algebra/L2/alg_gen_L2_026`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Ideal.Operations
import ABM.Cox.Cox_Chapter4_Ex.Cox_Chapter4_Section6_Definition_append
```

## Expected Declaration Names

- `irredundant_iInf_ideals_not_isPrime`

## Formalization Rules

```text
/-
Formalize in Lean the Theorem (irredundant_iInf_ideals_not_isPrime) from Text.

The theorem must be named `irredundant_iInf_ideals_not_isPrime`.
   Matched text (candidate 0, theorem, label=irredundant_iInf_ideals_not_isPrime): \begin{theorem}[irredundant_iInf_ideals_not_isPrime] Show that an irredundant intersection
                                                                                   of at least two prime ideals is never prime. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
