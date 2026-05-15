# ShadowBench Instructions: `geometry/L2/geo_gen_L2_017`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
```

## Expected Declaration Names

- `convex_partialSum`

## Formalization Rules

```text
open Set

/-
Formalize in Lean the Theorem (convex_partialSum) from Text.

The theorem must be named `convex_partialSum`.
   Matched text (candidate 0, theorem, label=convex_partialSum): \begin{theorem}[convex_partialSum] Show that if $S_1$ and $S_2$ are convex sets in
                                                                 $\mathbb{R}^{m+n}$, then so is their partial sum \[ S = \{(x, y_1 + y_2) \mid x \in
                                                                 \mathbb{R}^m, y_1, y_2 \in \mathbb{R}^n, (x, y_1) \in S_1, (x, y_2) \in S_2\}. \]
                                                                 \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
