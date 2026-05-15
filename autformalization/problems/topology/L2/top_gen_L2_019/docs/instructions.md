# ShadowBench Instructions: `topology/L2/top_gen_L2_019`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Perfect
```

## Expected Declaration Names

- `isTotallyDisconnected_cantorSet`

## Formalization Rules

```text
open Set Topology

/-
Formalize in Lean the Theorem (isTotallyDisconnected_cantorSet) from Text.

The theorem must be named `isTotallyDisconnected_cantorSet`.
   Matched text (candidate 0, theorem, label=isTotallyDisconnected_cantorSet): \begin{theorem}[isTotallyDisconnected_cantorSet] Prove that the Cantor set $\mathcal{C}$ is
                                                                               totally disconnected and perfect. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
