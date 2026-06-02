# Formalization Blueprint: `topology/L2/top_gen_L2_011`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib.Topology.VectorBundle.Basic
```

## Required Names

- `continuousLinearMap`
- `Bundle.ContinuousLinearMap.vectorBundle`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

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
