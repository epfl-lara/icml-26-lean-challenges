# ShadowBench Instructions: `geometry/L2/geo_gen_L2_003`

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
import Mathlib.Geometry.Euclidean.Projection
```

## Expected Declaration Names

- `erdos_mordell_inequality`

## Formalization Rules

```text
open Affine

/-
Formalize in Lean the named statement from the theorem in the text.

The Lean declaration must be named exactly:
- `erdos_mordell_inequality`

Matched text (candidate 0, theorem, label=erdos_mordell_inequality):
\begin{theorem}[erdos_mordell_inequality]\label{thm:erdos_mordell}
In Euclidean geometry, the Erdős–Mordell inequality states that for any triangle $ABC$ and point $P$ inside $ABC$, the sum of the distances from $P$ to the sides is less than or equal to half of the sum of the distances from $P$ to the vertices.
Let $PL, PM, PN$ be the perpendiculars from $P$ to the sides $BC, CA, AB$ respectively. Then:
\[
PA + PB + PC \ge 2(PL + PM + PN)
\]
\end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
