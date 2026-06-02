# ShadowBench Instructions: `geometry/L2/geo_gen_L2_015`

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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.Cone.Basic
```

## Expected Declaration Names

- `separatingHyperplanes_is_pointed`

## Formalization Rules

```text
open InnerProductSpace

/-
Formalize in Lean the Theorem (separatingHyperplanes_is_pointed) from Text.

The theorem must be named `separatingHyperplanes_is_pointed`.
   Matched text (candidate 0, theorem, label=separatingHyperplanes_is_pointed): \begin{theorem}[separatingHyperplanes_is_pointed] Suppose that $C$ and $D$ are disjoint
                                                                                subsets of $\mathbb{R}^n$. Consider the set of $(a, b) \in \mathbb{R}^{n+1}$ for which $a^T
                                                                                x \le b$ for all $x \in C$, and $a^T x \ge b$ for all $x \in D$. Show that this set is a
                                                                                convex cone containing the origin. (which is the singleton $\{0\}$ if there is no hyperplane
                                                                                that separates $C$ and $D$). \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
