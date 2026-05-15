# ShadowBench Instructions: `analysis/L4/ana_func_L4_003`

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

- `compactOpen_strictly_weaker_than_supNorm`

## Formalization Rules

```text
open scoped BoundedContinuousFunction

/-
Formalize in Lean the Theorem (compactOpen_strictly_weaker_than_supNorm) from Text.

The theorem must be named `compactOpen_strictly_weaker_than_supNorm`.
   Matched text (candidate 0, theorem, label=compactOpen_strictly_weaker_than_supNorm): \begin{theorem}[compactOpen_strictly_weaker_than_supNorm] Show that the compact open
                                                                                        topology is strictly weaker than the sup-norm topology on $C_b ([0, \infty) \to
                                                                                        \mathbb{C})$, the set of continuous bounded maps. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
