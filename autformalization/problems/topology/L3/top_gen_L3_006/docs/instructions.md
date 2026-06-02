# ShadowBench Instructions: `topology/L3/top_gen_L3_006`

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
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
```

## Expected Declaration Names

- `existsUnique_continuousMap_lifts`

## Formalization Rules

```text
open Topology unitInterval

/-
Formalize in Lean the Theorem (existsUnique_continuousMap_lifts) from Text.

The theorem must be named `existsUnique_continuousMap_lifts`.
   Matched text (candidate 0, theorem, label=existsUnique_continuousMap_lifts): \begin{theorem}[existsUnique_continuousMap_lifts] Let \(p:E\to X\) be a local homeomorphism.
                                                                                Let \(A\) be a path-connected and locally path-connected topological space. Let \[ f:A\to X
                                                                                \] be a continuous map, and fix points \(a_0\in A\) and \(e_0\in E\) such that \[
                                                                                p(e_0)=f(a_0). \] Assume the following two conditions. \begin{enumerate} \item For every
                                                                                path \(\gamma:I\to A\) with \(\gamma(0)=a_0\), there exists a p…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
