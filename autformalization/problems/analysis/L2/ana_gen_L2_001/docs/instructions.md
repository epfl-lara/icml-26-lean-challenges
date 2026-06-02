# ShadowBench Instructions: `analysis/L2/ana_gen_L2_001`

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
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
```

## Expected Declaration Names

- `MeromorphicAt`
- `AnalyticAt.meromorphicAt`

## Formalization Rules

```text
open Filter Set
open scoped Topology

/-
Formalize in Lean the following named items from Text.

1. Definition (MeromorphicAt)
   The definition must be named `MeromorphicAt`.
   Matched text (candidate 0, lemma): \begin{lemma} Let $\mathbb{K}$ be a nontrivially normed field and let $E$ be a normed vector
                                      space over $\mathbb{K}$. Let $f : \mathbb{K} \to E$ be an $E$-valued function on $\mathbb K$
                                      and let $x \in \mathbb{K}$. We say that $f$ is \emph{meromorphic at $x$} if there exists $n
                                      \in \mathbb{N}$ such that the function \[ z \longmapsto (z - x)^n f(z) \] is analytic at
                                      $x$. \end{lemma}
2. Lemma (AnalyticAt.meromorphicAt)
   The lemma must be named `AnalyticAt.meromorphicAt`.
   Matched text (candidate 1, theorem, label=AnalyticAt.meromorphicAt): \begin{theorem}[AnalyticAt.meromorphicAt] Let $f : \mathbb K \to E$ and let $x \in \mathbb
                                                                        K$. If $f$ is analytic at $x$, then $f$ is meromorphic at $x$. \end{theorem}

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
