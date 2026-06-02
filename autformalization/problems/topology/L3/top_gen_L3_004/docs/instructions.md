# ShadowBench Instructions: `topology/L3/top_gen_L3_004`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
```

## Expected Declaration Names

- `exists_lift_nhds`

## Formalization Rules

```text
open Topology unitInterval

/-
Formalize in Lean the Theorem (exists_lift_nhds) from Text.

The theorem must be named `exists_lift_nhds`.
   Matched text (candidate 0, theorem, label=exists_lift_nhds): \begin{theorem}[exists_lift_nhds] Let \(p : E \to X\) be a local homeomorphism. Denote the
                                                                unit interval \([0,1]\) by \(I\). Suppose \(f:I \times A \to X\) is a continuous map and \(g
                                                                : I \times A \to E\) is a lift of \(f\) continuous on \(\{0\} \times A \cup I \times \{a\}\)
                                                                for some $a \in A$. Then there exists a neighborhood \(N\) of \(a\) and \(g':I \times A \to
                                                                E\) continuous on \(I \times N\) that agrees with…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
