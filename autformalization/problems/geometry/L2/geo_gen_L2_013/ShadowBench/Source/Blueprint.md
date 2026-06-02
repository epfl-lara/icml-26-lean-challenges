# Formalization Blueprint: `geometry/L2/geo_gen_L2_013`

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
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding
```

## Required Names

- `gamma`
- `gamma_smooth`
- `gamma_is_embedding`
- `gamma_mfderiv_zero`
- `gamma_not_smooth_embedding`

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
open Manifold Set Topology

/-
Formalize in Lean the following named items from Text.

The text states one theorem about the map γ : ℝ → ℝ²,
γ(t) = (t^3, 0), saying that γ is smooth, is a topological embedding,
but is not a smooth embedding.

We split this theorem into the following Lean named items.

1. Definition (gamma)
   The definition must be named `gamma`.
   It should define the map γ : ℝ → ℝ² by
   γ(t) = (t^3, 0).

2. Theorem (gamma_smooth)
   The theorem must be named `gamma_smooth`.
   It should state that γ is a smooth map.

3. Theorem (gamma_is_embedding)
   The theorem must be named `gamma_is_embedding`.
   It should state that γ is a topological embedding.

4. Theorem (gamma_mfderiv_zero)
   The theorem must be named `gamma_mfderiv_zero`.
   It should state that the manifold derivative of γ at 0 is zero.

5. Theorem (gamma_not_smooth_embedding)
   The theorem must be named `gamma_not_smooth_embedding`.
   It should state that γ is not a smooth embedding.

Matched text (candidate 0, theorem, label=gamma_not_smooth_embedding):
\begin{theorem}[gamma_not_smooth_embedding]
Let $\gamma: \mathbb{R} \to \mathbb{R}^2$ be the map
$\gamma(t) = (t^3, 0)$. Show that $\gamma$ is a smooth map and a
topological embedding, but it is not a smooth embedding.
\end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
