# ShadowBench Instructions: `topology/L2/top_gen_L2_007`

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
import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.NoetherianSpace
```

## Expected Declaration Names

- `IsQuasiSeparated.image_of_isEmbedding`

## Formalization Rules

```text
open Set TopologicalSpace Topology

/-
Formalize in Lean the Theorem (IsQuasiSeparated.image_of_isEmbedding) from Text.

The theorem must be named `IsQuasiSeparated.image_of_isEmbedding`.
   Matched text (candidate 0, theorem, label=IsQuasiSeparated.image_of_isEmbedding): \begin{theorem}[IsQuasiSeparated.image_of_isEmbedding] Let $S \subseteq X$ be a
                                                                                     quasiseparated set and $h:X \to Y$ is a topological embedding. Then, $f(S)$ is
                                                                                     quasiseparated. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
