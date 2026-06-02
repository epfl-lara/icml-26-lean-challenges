# ShadowBench Instructions: `topology/L2/top_gen_L2_011`

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
import Mathlib.Topology.VectorBundle.Basic
```

## Expected Declaration Names

- `continuousLinearMap`
- `Bundle.ContinuousLinearMap.vectorBundle`

## Formalization Rules

```text
open Bundle Set ContinuousLinearMap Topology
open scoped Bundle

/-
Formalize in Lean the following named items from Text.

1. Definition (continuousLinearMap)
   The definition must be named `continuousLinearMap`.
   Matched text (candidate 0, definition, label=Bundle.ContinuousLinearMap.fiberBundle): \begin{definition}[Bundle.ContinuousLinearMap.fiberBundle] Let $E_1$, $E_2$ be vector
                                                                                         bundles over a base space $B$ with fibers $F_1$, $F_2$, respectively, where $F_i$ is a
                                                                                         normed space over a normed field $k_i$, for $i=1,2$. Let $\sigma: k_1 \to k_2$ be an
                                                                                         isometric ring homomorphism. The Hom-bundle $\text{Hom}_\sigma (E_1,E_2)$ is defined to be a
                                                                                         vector bundle over $B$ whose fiber $\text{Hom}_\sigma (E_1,E_2)_x$ i…
2. Theorem (Bundle.ContinuousLinearMap.vectorBundle)
   The theorem must be named `Bundle.ContinuousLinearMap.vectorBundle`.
   Matched text (candidate 1, theorem, label=Bundle.ContinuousLinearMap.vectorBundle): \begin{theorem}[Bundle.ContinuousLinearMap.vectorBundle] Let $E_1$, $E_2$ be vector bundles
                                                                                       over a base space $B$ with fibers $F_1$, $F_2$, respectively, where $F_i$ is a normed space
                                                                                       over a normed field $k_i$, for $i=1,2$. Let $\sigma: k_1 \to k_2$ be an isometric ring
                                                                                       homomorphism. The Hom-bundle $\text{Hom}_\sigma (E_1,E_2)$ inherits the natural structure of
                                                                                       a vector bundle. \end{theorem}

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
