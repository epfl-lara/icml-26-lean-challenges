# ShadowBench Instructions: `geometry/L3/geo_gen_L3_005`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.VectorBundle.Basic
```

## Expected Declaration Names

- `proj_homotopyEquiv`

## Formalization Rules

```text
open Bundle ContinuousMap Topology

/-
Formalize in Lean the Definition (proj_homotopyEquiv) from Text.

The definition must be named `proj_homotopyEquiv`.
   Matched text (candidate 0, definition, label=proj_homotopyEquiv): \begin{definition}[proj_homotopyEquiv] Let $E$ be a vector bundle over a topological space
                                                                     $M$. Show that the projection map $\pi : E \to M$ is a homotopy equivalence.
                                                                     \end{definition}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
