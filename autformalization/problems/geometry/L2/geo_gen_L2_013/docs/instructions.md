# ShadowBench Instructions: `geometry/L2/geo_gen_L2_013`

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
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding
```

## Expected Declaration Names

- `gamma`
- `gamma_smooth`
- `gamma_is_embedding`
- `gamma_mfderiv_zero`
- `gamma_not_smooth_embedding`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
