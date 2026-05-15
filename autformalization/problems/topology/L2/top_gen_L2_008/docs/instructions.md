# ShadowBench Instructions: `topology/L2/top_gen_L2_008`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.CategoryTheory.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
```

## Expected Declaration Names

- `paths_homotopic`
- `simply_connected_iff_paths_homotopic`

## Formalization Rules

```text
open CategoryTheory
open ContinuousMap
open scoped ContinuousMap

/-
Formalize in Lean the following named items from Text.

1. Theorem (paths_homotopic)
   The theorem must be named `paths_homotopic`.
   Matched text (candidate 0, theorem): \begin{theorem} A topological space $X$ is simply connected if its fundamental groupoid is
                                        equivalent to the the groupoid with one object and the identity morphism. \end{theorem}
2. Theorem (simply_connected_iff_paths_homotopic)
   The theorem must be named `simply_connected_iff_paths_homotopic`.
   Matched text (candidate 1, theorem, label=simply_connected_iff_paths_homotopic): \begin{theorem}[simply_connected_iff_paths_homotopic] A topological space is simply
                                                                                    connected if and only if it is path connected, and there is at most one path up to homotopy
                                                                                    between any two points. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
