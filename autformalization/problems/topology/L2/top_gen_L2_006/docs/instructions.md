# ShadowBench Instructions: `topology/L2/top_gen_L2_006`

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
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.UnitInterval
```

## Expected Declaration Names

- `monodromy_theorem`

## Formalization Rules

```text
open Topology unitInterval

/-
Formalize in Lean the Theorem (monodromy_theorem) from Text.

The theorem must be named `monodromy_theorem`.
   Matched text (candidate 0, theorem, label=monodromy_theorem): \begin{theorem}[monodromy_theorem] Let $\gamma_0,\gamma_1:I\to X$ be paths and let
                                                                 $\gamma:I\times I\to X$ be a homotopy rel.\ endpoints between them. Let $\Gamma:I\to C(I,E)$
                                                                 be a family of continuous paths in $E$ such that \[ p(\Gamma(t)(s))=\gamma(t,s)\quad \forall
                                                                 t,s\in I, \qquad \Gamma(t)(0)=\Gamma(0)(0)\quad \forall t\in I. \] Then
                                                                 $\Gamma(t)(1)=\Gamma(0)(1)$ for all $t\in I$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
