# ShadowBench Instructions: `Topology/L2/top_gen_L2_001`

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
import Mathlib.Order.KrullDimension
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds
```

## Expected Declaration Names

- `topologicalKrullDim`
- `IsInducing.topologicalKrullDim_le`
- `IsHomeomorph.topologicalKrullDim_eq`
- `topologicalKrullDim_subspace_le`

## Formalization Rules

```text
open Set Function Order TopologicalSpace Topology TopologicalSpace.IrreducibleCloseds

/-
Formalize in Lean the following named items from Text.


1. Definition (topologicalKrullDim)
   The definition must be named `topologicalKrullDim`.
   Matched text (candidate 1, paragraph): Let $T$ be a topological space. A chain of irreducible closed subsets of $T$ is a sequence
                                          $Z_0 \subset Z_1 \subset \cdots Z_n \subset T$ with $Z_i$ closed irreducible and $Z_i \ne
                                          Z_{i+1}$ for $i=0,\cdots,n-1$. The length of a chain $Z_0 \subset Z_1 \subset \cdots Z_n
                                          \subset T$ of irreducible closed subsets is the integer $n$. The Krull dimension
                                          $\text{dim}(T)$ of T is the supremum of lengths of chains of irreduc…
2. Theorem (IsInducing.topologicalKrullDim_le)
   The theorem must be named `IsInducing.topologicalKrullDim_le`.
   Matched text (candidate 3, paragraph): Theorem
3. Theorem (IsHomeomorph.topologicalKrullDim_eq)
   The theorem must be named `IsHomeomorph.topologicalKrullDim_eq`.
   Matched text (candidate 6, paragraph): If $Z_0 \subset Z_1 \subset \cdots Z_n \subset X$ is a chain of irreducible closed subsets
                                          of $X$, then $f^{-1}(Z_0) \subset f^{-1}(Z_1) \subset \cdots f^{-1}(Z_n) \subset Y$ is a
                                          chain of irreducible closed subsets of $Y$.
4. Theorem (topologicalKrullDim_subspace_le)
   The theorem must be named `topologicalKrullDim_subspace_le`.
   Matched text (candidate 11, paragraph): Theorem

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
