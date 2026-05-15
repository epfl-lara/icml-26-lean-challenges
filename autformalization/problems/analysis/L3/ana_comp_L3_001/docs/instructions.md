# ShadowBench Instructions: `analysis/L3/ana_comp_L3_001`

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

- `f`

## Formalization Rules

```text
/-
Formalize in Lean the Definition (f) from Text.

The definition must be named `f`.
   Matched text (candidate 0, definition, label=f): \begin{definition}[f] If $g(x)[e^{2y} - e^{-2y}]$ is harmonic, $g(0) = 0, g'(0) = 1$, find
                                                    $g(x)$. \end{definition}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
