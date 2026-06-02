# ShadowBench Instructions: `geometry/L2/geo_gen_L2_008`

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
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Defs
```

## Expected Declaration Names

- `smooth_function_separating_closed_sets`

## Formalization Rules

```text
open Set
open scoped ContDiff Manifold

/-
Formalize in Lean the Theorem (smooth_function_separating_closed_sets) from Text.

The theorem must be named `smooth_function_separating_closed_sets`.
   Matched text (candidate 0, theorem, label=smooth_function_separating_closed_sets): \begin{theorem}[smooth_function_separating_closed_sets] Suppose $A$ and $B$ are disjoint
                                                                                      closed subsets of a smooth manifold $M$. Show that there exists $f \in C^\infty(M)$ such
                                                                                      that $0 \le f(x) \le 1$ for all $x \in M$, $f^{-1}(0) = A$, and $f^{-1}(1) = B$.
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
